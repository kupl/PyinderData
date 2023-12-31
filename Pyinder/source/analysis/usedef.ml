open Core
open Pyre
open Ast
open Expression
open Statement

module TypeSet = Set.Make (Type)

module type UsedefState = sig
  type t [@@deriving show, sexp]

  val bottom : t

  val less_or_equal : left:t -> right:t -> bool

  val equal : t -> t -> bool

  val join : t -> t -> t

  val widen : previous:t -> next:t -> iteration:int -> t

  val get_used_before_defined : t -> TypeSet.t Reference.Map.t

  val get_defined : t -> TypeSet.t Reference.Map.t

  val get_used_after_defined : t -> TypeSet.t Reference.Map.t

  val to_vartypeset : t -> OurDomain.VarTypeSet.t

  val is_defined : t -> Reference.t -> bool

  val is_undefined : t -> Reference.t -> bool

  val forward : func_name:Reference.t -> statement_key:int -> post_info:(Resolution.t * Resolution.t) -> get_usedef_state_of_func:(Reference.t -> OurDomain.VarTypeSet.t) -> t -> statement:Statement.t -> t

  val backward : statement_key:int -> t -> statement:Statement.t -> t
end

module VarType = struct
  type t = Reference.t * Type.t [@@deriving sexp, compare]
end

module VarTypeSet = Set.Make (VarType)


module UsedefState = struct
  module VarSet = struct 
    type t = Reference.Set.t
    let empty = Reference.Set.empty
    let singleton name = Reference.Set.singleton name
    let union left right = Reference.Set.union left right

    let diff = Reference.Set.diff
    let inter left right = Reference.Set.inter left right
    let fold ~init ~f t = Reference.Set.fold t ~init ~f

    (* let iter = Reference.Set.iter *)

    let filter = Reference.Set.filter

    let exists = Reference.Set.exists
  end


  type usedef =
    | Use
    | Def 
    | CheckUse
    | CalleeDef of TypeSet.t
    | Both
  [@@deriving sexp]

  let usedef_equal left right =
    match left, right with
    | Use, Use | Def, Def | Both, Both | CheckUse, CheckUse -> true
    | CalleeDef left, CalleeDef right ->TypeSet.equal left right
    | _ -> false

  type t = { 
    used_before_defined : TypeSet.t Reference.Map.t;
    defined : TypeSet.t Reference.Map.t;
    check_used : TypeSet.t Reference.Map.t;
    used_after_defined : TypeSet.t Reference.Map.t;
    total : TypeSet.t Reference.Map.t;
    usedef_table : usedef Reference.Map.t;
  } [@@deriving sexp]

  let show _ = "Not Implemented"

  
  let pp_usedef format usedef =
    Format.fprintf format
    (match usedef with
    | Use -> "Use"
    | Def -> "Def"
    | CheckUse -> "CheckUse"
    | CalleeDef _ -> "CalleeDef"
    | Both -> "Both"
    ) 

  let pp_type_set format type_set =
    TypeSet.iter type_set ~f:(fun t -> Format.fprintf format "%a, " Type.pp t)

  let pp_table format table = 
    Reference.Map.iteri ~f:(fun ~key ~data -> 
      Format.fprintf format "%a -> %a\n" Reference.pp key pp_usedef data
    ) table

  let pp format t = 
    Format.fprintf format "%a\n\n" pp_table t.usedef_table;
    Format.fprintf format "[ CheckUsed Variables ] => \n";
    Reference.Map.iteri t.check_used ~f:(fun ~key ~data -> Format.fprintf format "%a => %a" Reference.pp key pp_type_set data);
    Format.fprintf format "\n";
    Format.fprintf format "[ Used Before Variables ] => \n";
    Reference.Map.iteri t.used_before_defined ~f:(fun ~key ~data -> Format.fprintf format "%a => %a" Reference.pp key pp_type_set data);
    Format.fprintf format "\n";
    Format.fprintf format "[ Defined Variables ] => \n";
    Reference.Map.iteri t.defined ~f:(fun ~key ~data -> Format.fprintf format "%a => %a" Reference.pp key pp_type_set data);
    Format.fprintf format "\n";
    Format.fprintf format "[ Used After Variables ] => \n";
    Reference.Map.iteri t.used_after_defined ~f:(fun ~key ~data -> Format.fprintf format "%a => %a" Reference.pp key pp_type_set data);
    Format.fprintf format "\n"

  

  
  let usedef_create = Reference.Map.empty

  let create = {
    used_before_defined=Reference.Map.empty;
    defined=Reference.Map.empty; 
    check_used=Reference.Map.empty;
    used_after_defined=Reference.Map.empty; 
    total=Reference.Map.empty; 
    usedef_table=usedef_create;
    }
  let bottom = create

  let less_or_equal ~left:_ ~right:_ = true

  let equal left right =
    Reference.Map.equal TypeSet.equal left.used_before_defined right.used_before_defined &&
    Reference.Map.equal TypeSet.equal left.defined right.defined &&
    Reference.Map.equal TypeSet.equal left.used_after_defined right.used_after_defined &&
    Reference.Map.equal usedef_equal left.usedef_table right.usedef_table

  let join left right = 
    let type_set_merge ~key:_ data =
      match data with
      | `Both (a, b) -> Some (TypeSet.union a b)
      | `Left a | `Right a -> Some a
    in

    let used_before_defined = Reference.Map.merge ~f:type_set_merge left.used_before_defined right.used_before_defined in
    let defined = (* Reference.Set.diff *) (Reference.Map.merge ~f:type_set_merge left.defined right.defined) (* undefined *) in
    let check_used = Reference.Map.merge ~f:type_set_merge left.check_used right.check_used in
    let used_after_defined =Reference.Map.merge ~f:type_set_merge left.used_after_defined right.used_after_defined in
    let total = Reference.Map.merge ~f:type_set_merge left.total right.total in
    { used_before_defined; defined; check_used; used_after_defined; total; usedef_table=usedef_create; }

  let widen ~previous:_ ~next ~iteration:_ = next

  let add_reference key varset =
    List.fold (Reference.possible_qualifiers key) ~init:(Reference.Set.add varset key) ~f:(fun varset k -> Reference.Set.add varset k)

  let get_used_before_defined { used_before_defined; _ } = used_before_defined

  let get_defined { defined; _ } = defined

  let get_used_after_defined { used_after_defined; _ } = used_after_defined

  let get_type_of_variable ~refinement reference =
    if Reference.is_self reference || Reference.is_cls reference
    then (
      let name, attribute_path = Reference.head reference |> Option.value ~default:Reference.empty, Reference.drop_head reference in
      (* Log.dump "Check %a %a" Reference.pp name Reference.pp attribute_path; *)
      let typ = Refinement.Store.get_annotation ~name ~attribute_path refinement in (* CAN???? *)
      typ >>| Annotation.annotation
    ) else (
      None
    ) 

  let get_use_variables usedef_table =
    Reference.Map.fold usedef_table ~init:Reference.Set.empty ~f:(fun ~key ~data varset ->
      match data with
      | Use | Both -> add_reference key varset
      | _ -> varset
    )

  let get_def_variables usedef_table = 
    Reference.Map.fold usedef_table ~init:Reference.Set.empty ~f:(fun ~key ~data varset ->
      match data with
      | Def | Both -> add_reference key varset
      | _ -> varset
    )

let get_both_variables usedef_table = 
    Reference.Map.fold usedef_table ~init:Reference.Set.empty ~f:(fun ~key ~data varset ->
      match data with
      | Both -> add_reference key varset
      | _ -> varset
    )

  let get_callee_def_variables_map usedef_table =
    Reference.Map.fold usedef_table ~init:Reference.Map.empty ~f:(fun ~key ~data varset ->
      match data with
      | CalleeDef type_set -> Reference.Map.set varset ~key ~data:type_set
      | _ -> varset
    )

  let get_check_use_variables usedef_table =
    Reference.Map.fold usedef_table ~init:Reference.Set.empty ~f:(fun ~key ~data varset ->
      match data with
      | CheckUse -> add_reference key varset
      | _ -> varset
    )

  let to_vartypeset { defined; _ } = 
    Reference.Map.fold defined ~init:OurDomain.VarTypeSet.empty ~f:(fun ~key ~data vartypeset ->
      let data = TypeSet.fold data ~init:OurDomain.TypeSet.empty ~f:(fun accum typ ->
        OurDomain.TypeSet.add accum typ
      ) in
      OurDomain.VarTypeSet.set ~key ~data vartypeset
    )
    

  let is_defined { defined; _ } reference =
    Reference.Map.mem defined reference

  let is_undefined t reference =
    not (is_defined t reference)

  let set_variables ~refinement ~init varset =
    let set_variable ~acc reference =
      (* let new_acc = 
        match Reference.drop_last reference with
        | reference when (Reference.is_self reference || Reference.is_cls reference) && (Reference.length reference > 1) ->
          set_variable ~acc reference
        | _ -> acc
      in *)
      let new_acc = acc in

      match get_type_of_variable ~refinement reference with
      | Some data ->
        Reference.Map.set new_acc ~key:reference ~data:(TypeSet.singleton data)
      | _ -> new_acc
    in

    Reference.Set.fold varset ~init ~f:(fun acc reference ->
      set_variable ~acc reference
    )

  let update_defined ~post_info:(_, post) t usedef_table =
    let type_set_merge ~key:_ data =
      match data with
      | `Both (a, b) -> Some (TypeSet.union a b)
      | `Left a | `Right a -> Some a
    in

    let defined_merge = Reference.Map.merge ~f:type_set_merge in

    (* let use_variables = get_use_variables usedef_table in *)
    let def_variables = get_def_variables usedef_table in 
    let callee_def_variables_map = get_callee_def_variables_map usedef_table in
    (* if all use variabels are defined, then put def variables in defined set *)
    (* let _ = if Reference.Set.is_subset use_variables ~of_:t.defined 
    then Reference.Set.union t.defined def_variables
    else t.defined
    in *)
    set_variables ~refinement:(Resolution.get_annotation_store post) ~init:t.defined def_variables
    |> defined_merge callee_def_variables_map

  let update_check_used ~post_info:(_, post) ~defined t usedef_table =

    let defined_diff =
      Reference.Map.symmetric_diff defined t.defined ~data_equal:TypeSet.equal
    in

    let filtered_check_used =
      Sequence.fold defined_diff ~init:t.check_used ~f:(fun acc (key, data) ->
        match data with
        | `Left _ | `Unequal _ ->
          Reference.Map.remove acc key
        | _ -> acc 
      )
    in

    (* let filtered_check_used = Reference.Map.mapi t.check_used ~f:(fun ~key ~data ->
      match Reference.Map.find defined key with
      | Some type_set -> TypeSet.diff data type_set
      | _ -> data
    ) |> Reference.Map.filter ~f:(fun data -> not (TypeSet.is_empty data))
    in *)
    
    let check_use_variables = get_check_use_variables usedef_table in
    set_variables ~refinement:(Resolution.get_annotation_store post) ~init:filtered_check_used check_use_variables

  let update_used_before_defined ~post_info:(pre, post) t usedef_table =
    let use_variables = get_use_variables usedef_table in
    let both_variables = get_both_variables usedef_table in
    let only_use_variables = Reference.Set.diff use_variables both_variables in
    let used_before_defined = 
      let before_defined_updated_only_use = 
        Reference.Set.filter only_use_variables ~f:(fun v -> not (Reference.Map.mem t.defined v))
        |> set_variables ~refinement:(Resolution.get_annotation_store post) ~init:t.used_before_defined
      in

      Reference.Set.filter both_variables ~f:(fun v -> not (Reference.Map.mem t.defined v))
        |> set_variables ~refinement:(Resolution.get_annotation_store pre) ~init:before_defined_updated_only_use
        
      (* Reference.Set.fold use_variables ~init:t.used_before_defined ~f:(fun used_before_defined use_variable -> 
      if Reference.Map.mem t.defined use_variable 
      then used_before_defined 
      else used_before_defined 
    )*)
    in
    used_before_defined
    (* if all use variabels are defined, then put def variables in defined set *)
    (* let _ =
    if Reference.Set.is_subset use_variables ~of_:t.defined 
    then undefined
    else  Reference.Set.union undefined def_variables
    in
    Reference.Set.diff undefined def_variables
 *)
 let update_used_after_defined ~post_info:(pre, post) t usedef_table =
  let use_variables = get_use_variables usedef_table in
  let def_variables = get_def_variables usedef_table in
  let both_variables = get_both_variables usedef_table in
  let only_use_variables = Reference.Set.diff use_variables both_variables in

  let after_defined_updated_only_use =
    Reference.Set.filter only_use_variables ~f:(fun v -> Reference.Map.mem t.defined v && not (Reference.Set.exists def_variables ~f:(Reference.equal v)))
    |> set_variables ~refinement:(Resolution.get_annotation_store pre) ~init:t.used_after_defined
  in

  Reference.Set.filter both_variables ~f:(fun v -> Reference.Map.mem t.defined v && not (Reference.Set.exists def_variables ~f:(Reference.equal v)))
  |> set_variables ~refinement:(Resolution.get_annotation_store post) ~init:after_defined_updated_only_use

  (* let used_after_defined = Reference.Set.fold use_variables ~init:t.used_after_defined ~f:(fun varset use_variable -> 
    if Reference.Set.mem t.defined use_variable then add_reference use_variable varset else varset
    |> (fun varset -> 
      if Reference.Set.mem defined use_variable then Reference.Set.remove varset use_variable else varset
    )
  )
  in *)
  

  let update_total t usedef_table =
    Reference.Map.fold usedef_table ~init:t.total ~f:(fun ~key:_ ~data:_ acc ->
      acc
    )

  let update_state ~post_info t usedef_table =
    let defined = update_defined ~post_info t usedef_table in
    let check_used = update_check_used ~post_info ~defined t usedef_table in
    let used_after_defined = update_used_after_defined ~post_info t usedef_table in
    let used_before_defined = update_used_before_defined ~post_info t usedef_table in
    {
      used_before_defined;
      defined;
      check_used;
      used_after_defined;
      total=update_total t usedef_table;
      usedef_table;
    }
  
    let rec forward_expression_type_check ~post_info (exp: Expression.t) =

      (* Log.dump "WOW : %a" Expression.pp exp; *)
  
      let forward_list expression_list f =
        List.fold ~init:VarSet.empty ~f:(fun accum e ->
          VarSet.union accum (f e)
        ) expression_list
      in
      let forward_generator (generator: Comprehension.Generator.t) =
        VarSet.union (forward_expression_type_check ~post_info generator.target) (forward_expression_type_check ~post_info generator.iterator)
        |> VarSet.union (forward_list generator.conditions (forward_expression_type_check ~post_info))
      in
      let forward_parameter (param: Parameter.t) =
        let param = Node.value param in
        VarSet.union 
          (Option.value_map param.value ~default:VarSet.empty ~f:(forward_expression_type_check ~post_info))
          (Option.value_map param.annotation ~default:VarSet.empty ~f:(forward_expression_type_check ~post_info))
      in
      let forward_expression_comprehension (comprehension: Expression.t Comprehension.t) =
        VarSet.union (forward_expression_type_check ~post_info comprehension.element) (forward_list comprehension.generators forward_generator)
      in
      match Node.value exp with
      | Name _ -> VarSet.empty
      | Await e -> forward_expression_type_check ~post_info e
      | BooleanOperator { left; operator=And; right; } ->
        let pre, _ = post_info in 
        let left_variables = forward_expression_type_check ~post_info left in
        let left_type = Resolution.resolve_expression_to_type pre left in
        if Type.is_falsy left_type
        then left_variables
        else (
          let right_variables = forward_expression_type_check ~post_info right in
          VarSet.union left_variables right_variables
        )
      | BooleanOperator { left; operator=Or; right; } ->
          let pre, _ = post_info in 
          let left_variables = forward_expression_type_check ~post_info left in
          let left_type = Resolution.resolve_expression_to_type pre left in
          if Type.is_truthy left_type
          then left_variables
          else (
            let right_variables = forward_expression_type_check ~post_info right in
            VarSet.union left_variables right_variables
          ) 
      (* | BooleanOperator e -> VarSet.union (forward_expression_type_check ~post_info e.left) (forward_expression_type_check ~post_info e.right) *)
      | Call
          {
            callee = { Node.value = Name (Name.Identifier "isinstance"); _ };
            arguments =
              [
                { Call.Argument.name = None; value = { Node.value = Name name; _ } };
                _
              ];
          }
        when is_simple_name name
        ->
          VarSet.singleton (name_to_reference_exn name)
      | Call e -> 
        let f accum (a: Call.Argument.t) =
          VarSet.union accum (forward_expression_type_check ~post_info a.value)
        in
        VarSet.union (forward_expression_type_check ~post_info e.callee) (List.fold ~init:VarSet.empty ~f e.arguments)
      | ComparisonOperator { left = { Node.value = Name name; _ }; operator= Is | IsNot; right = { Node.value = Constant _; _ }; } when is_simple_name name ->
        VarSet.singleton (name_to_reference_exn name)
      | ComparisonOperator { left = { Node.value = Name name; _ }; operator= Is | IsNot | In | NotIn; right; } when is_simple_name name
        ->
        forward_expression_type_check ~post_info right
      | ComparisonOperator { left = { Node.value = Constant (Constant.NoneLiteral); _ }; _ } 
        -> VarSet.empty
  
      | ComparisonOperator e -> VarSet.union (forward_expression_type_check ~post_info e.left) (forward_expression_type_check ~post_info e.right)
      | Dictionary e -> 
        let f accum (a: Dictionary.Entry.t) =
          VarSet.union accum (VarSet.union (forward_expression_type_check ~post_info a.key) (forward_expression_type_check ~post_info a.value))
        in
        VarSet.union (List.fold ~init:VarSet.empty ~f e.entries) (forward_list e.keywords (forward_expression_type_check ~post_info))
      | Generator e -> forward_expression_comprehension e
      | FormatString e -> forward_list e (fun e ->
          match e with
          | Format e -> forward_expression_type_check ~post_info e
          | _ -> VarSet.empty
        )
      | Lambda e -> VarSet.union (forward_list e.parameters forward_parameter) (forward_expression_type_check ~post_info e.body)
      | List e -> forward_list e (forward_expression_type_check ~post_info)
      | ListComprehension e -> forward_expression_comprehension e
      | Set e -> forward_list e (forward_expression_type_check ~post_info)
      | SetComprehension e -> forward_expression_comprehension e
      | Starred e ->
          (match e with
          | Once e | Twice e -> forward_expression_type_check ~post_info e
          )
      | Ternary e -> 
        VarSet.union (forward_expression_type_check ~post_info e.target) (forward_expression_type_check ~post_info e.alternative)
        |> (fun varset ->
          match e.target, e.test, e.alternative with
          | 
            { Node.value = Constant v1; _ },
            { Node.value = ComparisonOperator { left = { Node.value = Name _; _ }; operator= Is; right = { Node.value = Constant v2; _ }; }; _ },
            _ 
          | 
            _,
            { Node.value = ComparisonOperator { left = { Node.value = Name _; _ }; operator= IsNot; right = { Node.value = Constant v1; _ }; }; _ },
            { Node.value = Constant v2; _ }
            when Constant.location_insensitive_compare v1 v2 = 0
          -> varset
          | _ -> VarSet.union varset (forward_expression_type_check ~post_info e.test)  
        )
      | Tuple e -> forward_list e (forward_expression_type_check ~post_info)
      | UnaryOperator
          {
            UnaryOperator.operator = UnaryOperator.Not;
            operand = { Node.value = Name name; _ };
          } when is_simple_name name 
          -> VarSet.singleton (name_to_reference_exn name)
      | UnaryOperator e -> forward_expression_type_check ~post_info e.operand
      | WalrusOperator e -> VarSet.union (forward_expression_type_check ~post_info e.target) (forward_expression_type_check ~post_info e.value)
      | Yield (Some e) -> forward_expression_type_check ~post_info e
      | YieldFrom e -> forward_expression_type_check ~post_info e
      | _ -> VarSet.empty

  let rec forward_expression_call ~post_info ~get_usedef_state_of_func (exp: Expression.t) =

    (* let type_set_merge ~key:_ data =
      match data with
      | `Both (a, b) -> Some (TypeSet.union a b)
      | `Left a | `Right a -> Some a
    in *)

    let defined_merge = OurDomain.VarTypeSet.join in

    let forward_list expression_list f =
      List.fold ~init:OurDomain.VarTypeSet.empty ~f:(fun accum e ->
        defined_merge accum (f e)
      ) expression_list
    in
    let forward_generator (generator: Comprehension.Generator.t) =
      defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func generator.target) (forward_expression_call ~post_info ~get_usedef_state_of_func generator.iterator)
      |> defined_merge (forward_list generator.conditions (forward_expression_call ~post_info ~get_usedef_state_of_func))
    in
    let forward_parameter (param: Parameter.t) =
      let param = Node.value param in
      defined_merge 
        (Option.value_map param.value ~default:OurDomain.VarTypeSet.empty ~f:(forward_expression_call ~post_info ~get_usedef_state_of_func))
        (Option.value_map param.annotation ~default:OurDomain.VarTypeSet.empty ~f:(forward_expression_call ~post_info ~get_usedef_state_of_func))
    in
    let forward_expression_comprehension (comprehension: Expression.t Comprehension.t) =
      defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func comprehension.element) (forward_list comprehension.generators forward_generator)
    in
    match Node.value exp with
    | Await e -> forward_expression_call ~post_info ~get_usedef_state_of_func e
    | BooleanOperator { left; operator=And; right; } ->
      let pre, _ = post_info in 
      let left_variables = forward_expression_call ~post_info ~get_usedef_state_of_func left in
      let left_type = Resolution.resolve_expression_to_type pre left in
      if Type.is_falsy left_type
      then left_variables
      else (
        let right_variables = forward_expression_call ~post_info ~get_usedef_state_of_func right in
        defined_merge left_variables right_variables
      )
    | BooleanOperator { left; operator=Or; right; } ->
      let pre, _ = post_info in 
      let left_variables = forward_expression_call ~post_info ~get_usedef_state_of_func left in
      let left_type = Resolution.resolve_expression_to_type pre left in
      if Type.is_truthy left_type
      then left_variables
      else (
        let right_variables = forward_expression_call ~post_info ~get_usedef_state_of_func right in
        defined_merge left_variables right_variables
      ) 
    (* | BooleanOperator e -> 
      defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func e.left) (forward_expression_call ~post_info ~get_usedef_state_of_func e.right) *)

    | Call e -> 
      let f accum (a: Call.Argument.t) =
        (* For Use Condition *)
        match (Node.value a.value) with
        | Name name when is_simple_name name -> accum
        | _ ->
          defined_merge accum (forward_expression_call ~post_info ~get_usedef_state_of_func a.value)
      in

      let defined =
        match Node.value e.callee with
        | Name name when is_simple_name name && not (String.is_suffix ~suffix:"__" (Name.show name)) ->
          let pre, _ = post_info in
          (match Resolution.resolve_expression_to_type pre e.callee with
          | Type.Parametric { name = "BoundMethod"; parameters = [Single (Callable { kind = Named name; _ }); _]; _ } ->
            get_usedef_state_of_func name
          | _ -> OurDomain.VarTypeSet.empty
          )
        | _ -> OurDomain.VarTypeSet.empty
      in
      defined_merge defined (forward_expression_call ~post_info ~get_usedef_state_of_func e.callee)
      |> defined_merge (List.fold ~init:OurDomain.VarTypeSet.empty ~f e.arguments)
    | ComparisonOperator { left = { Node.value = Name name; _ }; operator= Is | IsNot | In | NotIn; right; } when is_simple_name name
      ->
      forward_expression_call ~post_info ~get_usedef_state_of_func right
    | ComparisonOperator { left = { Node.value = Constant (Constant.NoneLiteral); _ }; _ } 
      -> OurDomain.VarTypeSet.empty

    | ComparisonOperator e -> defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func e.left) (forward_expression_call ~post_info ~get_usedef_state_of_func e.right)
    | Dictionary e -> 
      let f accum (a: Dictionary.Entry.t) =
        defined_merge accum (defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func a.key) (forward_expression_call ~post_info ~get_usedef_state_of_func a.value))
      in
      defined_merge (List.fold ~init:OurDomain.VarTypeSet.empty ~f e.entries) (forward_list e.keywords (forward_expression_call ~post_info ~get_usedef_state_of_func))
    | Generator e -> forward_expression_comprehension e
    | FormatString e -> forward_list e (fun e ->
        match e with
        | Format e -> forward_expression_call ~post_info ~get_usedef_state_of_func e
        | _ -> OurDomain.VarTypeSet.empty
      )
    | Lambda e -> defined_merge (forward_list e.parameters forward_parameter) (forward_expression_call ~post_info ~get_usedef_state_of_func e.body)
    | List e -> forward_list e (forward_expression_call ~post_info ~get_usedef_state_of_func)
    | ListComprehension e -> forward_expression_comprehension e
    | Set e -> forward_list e (forward_expression_call ~post_info ~get_usedef_state_of_func)
    | SetComprehension e -> forward_expression_comprehension e
    | Starred e ->
        (match e with
        | Once e | Twice e -> forward_expression_call ~post_info ~get_usedef_state_of_func e
        )
    | Ternary e -> defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func e.target) (forward_expression_call ~post_info ~get_usedef_state_of_func e.test) |> defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func e.alternative)
    | Tuple e -> forward_list e (forward_expression_call ~post_info ~get_usedef_state_of_func)
    | UnaryOperator
        {
          UnaryOperator.operator = UnaryOperator.Not;
          operand = { Node.value = Name name; _ };
        } when is_simple_name name 
        -> OurDomain.VarTypeSet.empty
    | UnaryOperator e -> forward_expression_call ~post_info ~get_usedef_state_of_func e.operand
    | WalrusOperator e -> defined_merge (forward_expression_call ~post_info ~get_usedef_state_of_func e.target) (forward_expression_call ~post_info ~get_usedef_state_of_func e.value)
    | Yield (Some e) -> forward_expression_call ~post_info ~get_usedef_state_of_func e
    | YieldFrom e -> forward_expression_call ~post_info ~get_usedef_state_of_func e
    | _ -> OurDomain.VarTypeSet.empty

  let rec forward_expression ~post_info (exp: Expression.t) =

    (* Log.dump "WOW : %a" Expression.pp exp; *)

    let forward_list expression_list f =
      List.fold ~init:VarSet.empty ~f:(fun accum e ->
        VarSet.union accum (f e)
      ) expression_list
    in
    let forward_generator (generator: Comprehension.Generator.t) =
      VarSet.union (forward_expression ~post_info generator.target) (forward_expression ~post_info generator.iterator)
      |> VarSet.union (forward_list generator.conditions (forward_expression ~post_info))
    in
    let forward_parameter (param: Parameter.t) =
      let param = Node.value param in
      VarSet.union 
        (Option.value_map param.value ~default:VarSet.empty ~f:(forward_expression ~post_info))
        (Option.value_map param.annotation ~default:VarSet.empty ~f:(forward_expression ~post_info))
    in
    let forward_expression_comprehension (comprehension: Expression.t Comprehension.t) =
      VarSet.union (forward_expression ~post_info comprehension.element) (forward_list comprehension.generators forward_generator)
    in
    match Node.value exp with
    | Name n -> 
      (match name_to_reference n with
      | Some name -> (* Log.dump "HMM : %a" Reference.pp name; *) VarSet.singleton name
      | None -> (* Log.dump "WHAT?? : %a" Name.pp n; *) VarSet.empty
      )
    | Await e -> forward_expression ~post_info e
    | BooleanOperator { left; operator=And; right; } ->
      let pre, _ = post_info in 
      let left_variables = forward_expression ~post_info left in
      let left_type = Resolution.resolve_expression_to_type pre left in
      if Type.is_falsy left_type
      then left_variables
      else (
        let right_variables = forward_expression ~post_info right in
        VarSet.union left_variables right_variables
      )
    | BooleanOperator { left; operator=Or; right; } ->
      let pre, _ = post_info in 
      let left_variables = forward_expression ~post_info left in
      let left_type = Resolution.resolve_expression_to_type pre left in
      if Type.is_truthy left_type
      then left_variables
      else (
        let right_variables = forward_expression ~post_info right in
        VarSet.union left_variables right_variables
      ) 
    (* | BooleanOperator e -> 
      VarSet.union (forward_expression ~post_info e.left) (forward_expression ~post_info e.right) *)
    | Call
        {
          callee = { Node.value = Name (Name.Identifier "isinstance"); _ };
          arguments =
            [
              { Call.Argument.name = None; value = { Node.value = Name name; _ } };
              _
            ];
        }
      when is_simple_name name
      ->
        VarSet.empty
    | Call
        {
          callee = { Node.value = Name (Name.Attribute { base = { Node.value = Constant String _; _}; attribute = "format"; _ }); _ };
          arguments;
        }
        ->
        let f accum (a: Call.Argument.t) =
          (* For Use Condition *)
          match (Node.value a.value) with
          | Name name when is_simple_name name -> 
            VarSet.union accum (VarSet.singleton (name_to_reference_exn name))
          | _ ->
            VarSet.union accum (forward_expression ~post_info a.value)
        in
        (List.fold ~init:VarSet.empty ~f arguments)
    | Call e -> 
      let f accum (a: Call.Argument.t) =
        (* For Use Condition *)
        match (Node.value a.value) with
        | Name name when is_simple_name name -> accum
        | _ ->
          VarSet.union accum (forward_expression ~post_info a.value)
      in
      VarSet.union (forward_expression ~post_info e.callee) (List.fold ~init:VarSet.empty ~f e.arguments)
    | ComparisonOperator { left = { Node.value = Name name; _ }; operator= Is | IsNot | In | NotIn; right; } when is_simple_name name
      ->
      forward_expression ~post_info right
    | ComparisonOperator { left = { Node.value = Constant (Constant.NoneLiteral); _ }; _ } 
      -> VarSet.empty

    | ComparisonOperator e -> VarSet.union (forward_expression ~post_info e.left) (forward_expression ~post_info e.right)
    | Dictionary e -> 
      let f accum (a: Dictionary.Entry.t) =
        VarSet.union accum (VarSet.union (forward_expression ~post_info a.key) (forward_expression ~post_info a.value))
      in
      VarSet.union (List.fold ~init:VarSet.empty ~f e.entries) (forward_list e.keywords (forward_expression ~post_info))
    | Generator e -> forward_expression_comprehension e
    | FormatString e -> forward_list e (fun e ->
        match e with
        | Format e -> forward_expression ~post_info e
        | _ -> VarSet.empty
      )
    | Lambda e -> VarSet.union (forward_list e.parameters forward_parameter) (forward_expression ~post_info e.body)
    | List e -> forward_list e (forward_expression ~post_info)
    | ListComprehension e -> forward_expression_comprehension e
    | Set e -> forward_list e (forward_expression ~post_info)
    | SetComprehension e -> forward_expression_comprehension e
    | Starred e ->
        (match e with
        | Once e | Twice e -> forward_expression ~post_info e
        )
    | Ternary e -> 
      let type_check_variable = forward_expression_type_check ~post_info e.test in
      let varset = 
        VarSet.union (forward_expression ~post_info e.target) (forward_expression ~post_info e.test) 
        |> VarSet.union (forward_expression ~post_info e.alternative)
      in

      VarSet.filter varset ~f:(fun r -> 
        not (VarSet.exists type_check_variable ~f:(fun tr -> Reference.is_contain ~base:r ~target:tr))
      )  
      
    | Tuple e -> forward_list e (forward_expression ~post_info)
    | UnaryOperator
        {
          UnaryOperator.operator = UnaryOperator.Not;
          operand = { Node.value = Name name; _ };
        } when is_simple_name name 
        -> VarSet.empty
    | UnaryOperator e -> forward_expression ~post_info e.operand
    | WalrusOperator e -> VarSet.union (forward_expression ~post_info e.target) (forward_expression ~post_info e.value)
    | Yield (Some e) -> forward_expression ~post_info e
    | YieldFrom e -> forward_expression ~post_info e
    | _ -> VarSet.empty


  let forward_assignment ~target ~value ~post_info ~get_usedef_state_of_func usedef_map =

    let target_variables = forward_expression ~post_info target in
    let value_variables = forward_expression ~post_info value in
    let type_check_variables = forward_expression_type_check ~post_info value in
    let callee_vartypes = forward_expression_call ~post_info ~get_usedef_state_of_func value in

    let filter_simple_assign value_variables value =
      match Node.value value with
      | Expression.Name n -> (
        match name_to_reference n with
        | Some _ -> VarSet.empty
        | _ -> value_variables
      )
      | _ -> value_variables
    in

    (* Log.dump "ASSIGN : %a" Expression.pp value;
    VarSet.iter value_variables ~f:(fun v -> Log.dump "VARIABLE : %a" Reference.pp v);
    VarSet.iter type_check_variables ~f:(fun v -> Log.dump "TYPE CHECK : %a" Reference.pp v); *)

    let value_variables = filter_simple_assign value_variables value in

    let both_variables = VarSet.inter target_variables value_variables in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Def) target_variables in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Use) (VarSet.diff value_variables type_check_variables) in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Both) both_variables in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:CheckUse) type_check_variables in
    let usedef_map = OurDomain.VarTypeSet.fold ~init:usedef_map ~f:(fun ~key ~data usedef_map -> 
      (* Log.dump "HMM %a" Reference.pp key; *)
      let data = OurDomain.TypeSet.fold ~init:TypeSet.empty ~f:(fun acc data -> TypeSet.add acc data) data in
      Reference.Map.set usedef_map ~key ~data:(CalleeDef data)) callee_vartypes in
    usedef_map

  let forward_assert ~post_info test usedef_map =
    let test_variables = forward_expression ~post_info test in
    let type_check_variables = forward_expression_type_check ~post_info test in

    (* let pre, _ = post_info in
    Log.dump "%a ==>" Expression.pp test;
    Reference.Set.iter test_variables ~f:(fun r -> Log.dump "%a, " Reference.pp r);
    Log.dump "%a" Resolution.pp pre; *)

    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Use) (VarSet.diff test_variables type_check_variables) in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:CheckUse) type_check_variables in
    usedef_map

  let forward_only_expression ~post_info ~get_usedef_state_of_func exp usedef_map =
    let test_variables = forward_expression ~post_info exp in
    let type_check_variables = forward_expression_type_check ~post_info exp in
    let callee_vartypes = forward_expression_call ~post_info ~get_usedef_state_of_func exp in

    (* let pre, _ = post_info in
    Log.dump "%a ==>" Expression.pp test;
    Reference.Set.iter test_variables ~f:(fun r -> Log.dump "%a, " Reference.pp r);
    Log.dump "%a" Resolution.pp pre; *)

    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Use) (VarSet.diff test_variables type_check_variables) in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:CheckUse) type_check_variables in
    let usedef_map = OurDomain.VarTypeSet.fold ~init:usedef_map ~f:(fun ~key ~data usedef_map -> 
      let data = OurDomain.TypeSet.fold ~init:TypeSet.empty ~f:(fun acc data -> TypeSet.add acc data) data in
      Reference.Map.set usedef_map ~key ~data:(CalleeDef data)) callee_vartypes in
    usedef_map

  let forward_setitem ~callee ~(value: Call.Argument.t) ~post_info usedef_map =
    let target_variables = forward_expression ~post_info callee in
    let value_variables = forward_expression ~post_info value.value in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Def) target_variables in
    let usedef_map = VarSet.fold ~init:usedef_map ~f:(fun usedef_map key -> Reference.Map.set usedef_map ~key ~data:Use) value_variables in
    usedef_map
    

  let forward_statement ~func_name ~(statement: Statement.t) ~post_info ~get_usedef_state_of_func state =

    (* Log.dump "WHY %a" Statement.pp statement; *)

    match Node.value statement with
    | Assign { Assign.target; value; _} ->
      forward_assignment ~target ~value ~post_info ~get_usedef_state_of_func state
    | Assert { 
      Assert.test = { Node.value=ComparisonOperator { left = { Node.value = Name _; _ }; operator= Is | IsNot; right = { Node.value = Constant _; _ }; }; _}; 
      origin=(Assert.Origin.If { true_branch }) | (Assert.Origin.While { true_branch });  
      _ } when (not true_branch) && not (String.equal (Reference.last func_name) "__init__") -> 
      state
    | Assert { Assert.test; _ } -> 
      (* Log.dump "HMM? %a" Expression.pp test ; *)
      forward_assert ~post_info test state
    | Expression { Node.value = Call { 
        callee = {
            Node.value = Name (Attribute {
                attribute="__setitem__"; _
              }
            );
            _
          } as callee;
        arguments= [ _; value ];
        };
        _
      } ->
        forward_setitem ~callee ~value ~post_info state
    | Expression exp ->
      forward_only_expression ~post_info ~get_usedef_state_of_func exp state
    | Return { expression=exp; _ } ->
      (match exp with
      | Some { Node.value = Name name; _ } when is_simple_name name -> state
      | Some exp -> forward_assert ~post_info exp state
      | _ -> state
      )
    | _ -> 
      (* Log.dump "HMM? %a" Statement.pp statement; *)
      state

  let forward ~func_name ~statement_key:_ ~post_info ~get_usedef_state_of_func state ~statement =
    let usedef_table = forward_statement ~func_name ~statement ~post_info ~get_usedef_state_of_func usedef_create in
    

    let x = update_state ~post_info state usedef_table in
    (* Log.dump "STATEMENT %a\n\nBEFOOORE %a\n\nAFFFTER %a\n" Statement.pp statement pp state pp x; *)
    x

  let backward ~statement_key:_ state ~statement:_ =
    state

end

module type UsedefFixpoint = sig
  type state

  type t = {
    usedef_tables: state Int.Table.t
  }
  [@@deriving show, sexp, equal]

  val entry : t -> state option

  val normal_exit : t -> state option

  val exit : t -> state option

  val empty : t

  val get_usedef_tables : t -> state Int.Table.t

  val find : t -> int -> state option

  val find_usedef_table_of_location : t -> Cfg.t -> Location.t -> state option

  val forward : func_name:Reference.t -> cfg:Cfg.t -> post_info:(Resolution.t option * Resolution.t option) Int.Map.t -> initial:state -> 
    get_usedef_state_of_func:(Reference.t -> OurDomain.VarTypeSet.t) -> t

  val forward_for_exception : cfg:Cfg.t -> post_info:(Resolution.t option * Resolution.t option) Int.Map.t -> initial:state -> 
    get_usedef_state_of_func:(Reference.t -> OurDomain.VarTypeSet.t) -> t

  val backward : cfg:Cfg.t -> initial:state -> t

  (*
  val equal : f:(state -> state -> bool) -> t -> t -> bool
*)
end

module Make (State : UsedefState) = struct
  type state = State.t


  type t = {
    usedef_tables: State.t Int.Table.t;
    (* used_tables: state Int.Table.t; *)
  } [@@deriving sexp, equal]

  (*
  let equal ~f left right =
    Core.Hashtbl.equal f left.usedef_tables right.usedef_tables
  *)

  (* let pp_vartype_set format vartype_set =
    VarTypeSet.iter vartype_set ~f:(fun (var, typ) ->
      Format.fprintf format "%a ---> %a\n" Reference.pp var Type.pp typ
    )
 *)
  let pp format { usedef_tables; } =
    let print_state ~name ~key ~data =
      Format.fprintf format "%s %d -> \n%a\n" name key State.pp data
    in
    Hashtbl.iteri usedef_tables ~f:(print_state ~name:"UseDef")

  let show fixpoint = Format.asprintf "%a" pp fixpoint

  let find { usedef_tables; _ } node_id = Hashtbl.find usedef_tables node_id
  let entry { usedef_tables; _ } = Hashtbl.find usedef_tables Cfg.entry_index

  let normal_exit { usedef_tables; _ } = Hashtbl.find usedef_tables Cfg.normal_index

  let exit { usedef_tables; _ } = Hashtbl.find usedef_tables Cfg.exit_index

  let empty = { usedef_tables=Int.Table.create (); }

  let get_usedef_tables { usedef_tables; _ } = usedef_tables

(*   let check_usdef_vartype ~post_info:(prev_refinement, post_refinement) state =
    let new_used_before_defined = State.get_used_before_defined state in
    let new_used_after_defined = State.get_used_after_defined state in

    Reference.Set.iter new_used_before_defined ~f:(fun r -> Log.dump "BEFORE %a" Reference.pp r);
    Reference.Set.iter new_used_after_defined ~f:(fun r -> Log.dump "AFTER %a" Reference.pp r);

    Log.dump "REFINEMNT BEFORE : %a" Refinement.Store.pp prev_refinement;
    Log.dump "REFINEMNT AFTER : %a" Refinement.Store.pp post_refinement;

    let var_type_set =
      Reference.Set.fold new_used_before_defined ~init:VarTypeSet.empty ~f:(fun var_type_set ref ->
        if Reference.is_self ref || Reference.is_cls ref
        then (
          let name, attribute_path = Reference.head ref |> Option.value ~default:Reference.empty, Reference.drop_head ref in
          (* Log.dump "Check %a %a" Reference.pp name Reference.pp attribute_path; *)
          let _ = prev_refinement in
          let typ = Refinement.Store.get_annotation ~name ~attribute_path prev_refinement in (* CAN???? *)
          (match typ with
          | Some t -> VarTypeSet.add var_type_set (ref, Annotation.annotation t)
          | _ -> var_type_set
          )
        ) else (
          var_type_set
        ) 
      )
    in

    let var_type_set =
      Reference.Set.fold new_used_after_defined ~init:var_type_set ~f:(fun var_type_set ref ->
        if Reference.is_self ref || Reference.is_cls ref
        then (
          let name, attribute_path = Reference.head ref |> Option.value ~default:Reference.empty, Reference.drop_head ref in
          let typ = Refinement.Store.get_annotation ~name ~attribute_path post_refinement in
          (match typ with
          | Some t -> VarTypeSet.add var_type_set (ref, Annotation.annotation t)
          | _ -> var_type_set
          )
        ) else (
          var_type_set
        ) 
      )
    in

    VarTypeSet.iter var_type_set ~f:(fun (ref, typ) -> Log.dump "RESULT (%a => %a)" Reference.pp ref Type.pp typ);

    var_type_set *)

  let find_usedef_table_of_location t (cfg: Cfg.t) location =
    Int.Table.fold cfg ~init:None ~f:(fun ~key:node_id ~data:node state ->
      if Option.is_some state then state
      else
        let statements = Cfg.Node.statements node in
        List.fold statements ~init:state ~f:(fun state statement -> 
          let start_contains = Location.contains_eq ~location:(Node.location statement) (Location.start location) in
          let stop_contains = Location.contains_eq ~location:(Node.location statement) (Location.stop location) in
          if start_contains && stop_contains then find t node_id else state
        )
    )


  let our_compute_fixpoint cfg ~initial_index ~initial ~post_info ~predecessors ~successors ~transition =
    (*
     * This is the implementation of a monotonically increasing chaotic fixpoint
     * iteration sequence with widening over a control-flow graph (CFG) using the
     * recursive iteration strategy induced by a weak topological ordering of the
     * nodes in the control-flow graph. The recursive iteration strategy is
     * described in Bourdoncle's paper on weak topological orderings:
     *
     *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
     *   In Formal Methods in Programming and Their Applications, pp 128-141.
     *)
    let components = WeakTopologicalOrder.create ~cfg ~entry_index:initial_index ~successors in

    let usedef_tables = Int.Table.create () in

    let join_with_predecessors_usedef_tables node state =
      if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
          predecessors node
          |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
                Hashtbl.find usedef_tables predecessor_index
                |> Option.value ~default:State.bottom
                |> State.join sofar)
      
      (* if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
          predecessors node
          |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
                Hashtbl.find usedef_tables predecessor_index
                |> Option.value ~default:State.bottom
                |> State.join sofar) *)
    in

    let analyze_node node =
      let node_id = Cfg.Node.id node in
      let usedef_table = 
        match Int.Map.find post_info (Cfg.Node.id node) with
        | Some (Some pre, Some post) ->
          let usedef_table = 
            Hashtbl.find usedef_tables node_id
            |> Option.value ~default:State.bottom
            |> join_with_predecessors_usedef_tables node
          in
          (* Log.dump "CHECK NODE : %a" Cfg.Node.pp node; *)
          let usedef_table = transition ~post_info:(pre, post) node_id usedef_table (Cfg.Node.statements node) in

          (* Log.dump "===> %a" State.pp usedef_table; *)

          usedef_table
          
          (* check_usdef_vartype ~post_info usedef_table *)
        | _ -> State.bottom
      in
      (* let usedef_table =
        usedef_table
        |> join_with_predecessors_usedef_tables node
      in *)
      (* Log.dump "[[[ USEDEF TABLE: Node %d ]]] \n\n%a\n\n" node_id pp_vartype_set usedef_table; *)
      Hashtbl.set usedef_tables ~key:node_id ~data:usedef_table;

    in
    let rec analyze_component = function
      | { WeakTopologicalOrder.Component.kind = Node node; _ } -> 
        analyze_node node
      | { kind = Cycle { head; components }; _ } ->
          (* Loop에 해당하는 거 같음 *)
          let head_id = Cfg.Node.id head in
          let rec iterate local_iteration =
            analyze_node head;
            List.iter ~f:analyze_component components;
            let current_head_precondition = Hashtbl.find_exn usedef_tables head_id in
            let new_head_precondition =
              join_with_predecessors_usedef_tables head current_head_precondition
            in

            let converged =
              (* VarTypeSet.is_subset new_head_precondition ~of_:current_head_precondition *)
              State.less_or_equal ~left:new_head_precondition ~right:current_head_precondition
            in
            (* Log.log
              ~section:`Fixpoint
              "\n%a\n  { <= (result %b) (iteration = %d) }\n\n%a"
              State.pp
              new_head_precondition
              converged
              local_iteration
              State.pp
              current_head_precondition; *)
            if not converged then (
              let precondition =
                (* VarTypeSet.union current_head_precondition new_head_precondition *)
                State.widen
                  ~previous:current_head_precondition
                  ~next:new_head_precondition
                  ~iteration:local_iteration
              in
              Hashtbl.set usedef_tables ~key:head_id ~data:precondition;
              iterate (local_iteration + 1))
            else
              (* At this point, we know we have a local fixpoint.
               * Since operators are monotonic, `new_head_precondition` is also
               * a post fixpoint. This is basically the argument for performing
               * decreasing iteration sequence with a narrowing operator.
               * Therefore, `new_head_precondition` might be more precise,
               * let's use it at the result.
               *)
              Hashtbl.set usedef_tables ~key:head_id ~data:new_head_precondition
          in
          iterate 0
    in
    List.iter ~f:analyze_component components;

    (*
    Hashtbl.iteri class_hierachy ~f:(fun ~key:ref ~data:define_list -> 
      Format.printf "[Reference] \n %a \n" Reference.pp ref;
      Hashtbl.iteri define_list ~f:(fun ~key:define ~data:summary ->
        Format.printf "\n %a \n" Define.pp define;
        Format.printf "\n %a \n" Summary.pp summary;
      );
    );
    *)
    

    { usedef_tables; }

let our_compute_fixpoint_for_exception cfg ~initial_index ~initial ~post_info ~predecessors ~successors ~transition =
    (*
     * This is the implementation of a monotonically increasing chaotic fixpoint
     * iteration sequence with widening over a control-flow graph (CFG) using the
     * recursive iteration strategy induced by a weak topological ordering of the
     * nodes in the control-flow graph. The recursive iteration strategy is
     * described in Bourdoncle's paper on weak topological orderings:
     *
     *   F. Bourdoncle. Efficient chaotic iteration strategies with widenings.
     *   In Formal Methods in Programming and Their Applications, pp 128-141.
     *)
    let components = WeakTopologicalOrder.create ~cfg ~entry_index:initial_index ~successors in

    let usedef_tables = Int.Table.create () in

    let join_with_predecessors_usedef_tables node state =
      if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
          predecessors node
          |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
                Hashtbl.find usedef_tables predecessor_index
                |> Option.value ~default:State.bottom
                |> State.join sofar)
      
      (* if Int.equal (Cfg.Node.id node) initial_index then
        State.join state initial
      else
          predecessors node
          |> Set.fold ~init:state ~f:(fun sofar predecessor_index ->
                Hashtbl.find usedef_tables predecessor_index
                |> Option.value ~default:State.bottom
                |> State.join sofar) *)
    in

    let analyze_node node =
      let node_id = Cfg.Node.id node in
      let usedef_table = 
        Hashtbl.find usedef_tables node_id
        |> Option.value ~default:State.bottom
        |> join_with_predecessors_usedef_tables node
      in

      let usedef_table = 
        match Int.Map.find post_info (Cfg.Node.id node) with
        | Some (Some pre, None) ->
          transition ~post_info:(pre, pre) node_id usedef_table (Cfg.Node.statements node)
        | _ -> usedef_table
      in
      (* let usedef_table =
        usedef_table
        |> join_with_predecessors_usedef_tables node
      in *)
      (* Log.dump "[[[ USEDEF TABLE: Node %d ]]] \n\n%a\n\n" node_id pp_vartype_set usedef_table; *)
      Hashtbl.set usedef_tables ~key:node_id ~data:usedef_table;

    in
    let rec analyze_component = function
      | { WeakTopologicalOrder.Component.kind = Node node; _ } -> 
        analyze_node node
      | { kind = Cycle { head; components }; _ } ->
          (* Loop에 해당하는 거 같음 *)
          let head_id = Cfg.Node.id head in
          let rec iterate local_iteration =
            analyze_node head;
            List.iter ~f:analyze_component components;
            let current_head_precondition = Hashtbl.find_exn usedef_tables head_id in
            let new_head_precondition =
              join_with_predecessors_usedef_tables head current_head_precondition
            in

            let converged =
              (* VarTypeSet.is_subset new_head_precondition ~of_:current_head_precondition *)
              State.less_or_equal ~left:new_head_precondition ~right:current_head_precondition
            in
            (* Log.log
              ~section:`Fixpoint
              "\n%a\n  { <= (result %b) (iteration = %d) }\n\n%a"
              State.pp
              new_head_precondition
              converged
              local_iteration
              State.pp
              current_head_precondition; *)
            if not converged then (
              let precondition =
                (* VarTypeSet.union current_head_precondition new_head_precondition *)
                State.widen
                  ~previous:current_head_precondition
                  ~next:new_head_precondition
                  ~iteration:local_iteration
              in
              Hashtbl.set usedef_tables ~key:head_id ~data:precondition;
              iterate (local_iteration + 1))
            else
              (* At this point, we know we have a local fixpoint.
               * Since operators are monotonic, `new_head_precondition` is also
               * a post fixpoint. This is basically the argument for performing
               * decreasing iteration sequence with a narrowing operator.
               * Therefore, `new_head_precondition` might be more precise,
               * let's use it at the result.
               *)
              Hashtbl.set usedef_tables ~key:head_id ~data:new_head_precondition
          in
          iterate 0
    in
    List.iter ~f:analyze_component components;

    (*
    Hashtbl.iteri class_hierachy ~f:(fun ~key:ref ~data:define_list -> 
      Format.printf "[Reference] \n %a \n" Reference.pp ref;
      Hashtbl.iteri define_list ~f:(fun ~key:define ~data:summary ->
        Format.printf "\n %a \n" Define.pp define;
        Format.printf "\n %a \n" Summary.pp summary;
      );
    );
    *)
    

    { usedef_tables; }

  let forward ~func_name ~cfg ~post_info ~initial ~get_usedef_state_of_func =
    let transition ~post_info node_id init statements =
      let forward statement_index before statement =
        let statement_key = [%hash: int * int] (node_id, statement_index) in
        let after = State.forward ~func_name ~statement_key ~post_info ~get_usedef_state_of_func before ~statement in
        (*
        Format.printf "\n\n  {  %a  } \n\n"
        Statement.pp
        statement
        ;
        *)
        (*Log.log
          ~section:`Fixpoint
          "\n%a\n  {  %a  }\n\n%a"
          State.pp
          before
          Statement.pp
          statement
          State.pp
          after;*)
        after
      in
      List.foldi ~f:forward ~init statements
    in
    our_compute_fixpoint
      cfg
      ~initial_index:Cfg.entry_index
      ~initial
      ~post_info
      ~predecessors:Cfg.Node.predecessors
      ~successors:Cfg.Node.successors
      ~transition

  let forward_for_exception ~cfg ~post_info ~initial ~get_usedef_state_of_func =
    let transition ~post_info node_id init statements =
      let forward statement_index before statement =
        let statement_key = [%hash: int * int] (node_id, statement_index) in
        let after = State.forward ~func_name:Reference.empty ~statement_key ~post_info ~get_usedef_state_of_func before ~statement in
        (*
        Format.printf "\n\n  {  %a  } \n\n"
        Statement.pp
        statement
        ;
        *)
        (*Log.log
          ~section:`Fixpoint
          "\n%a\n  {  %a  }\n\n%a"
          State.pp
          before
          Statement.pp
          statement
          State.pp
          after;*)
        after
      in
      List.foldi ~f:forward ~init statements
    in
    our_compute_fixpoint_for_exception
      cfg
      ~initial_index:Cfg.entry_index
      ~initial
      ~post_info
      ~predecessors:Cfg.Node.predecessors
      ~successors:Cfg.Node.successors
      ~transition
    (*
  let our_forward ~cfg ~initial =
    let transition node_id init statements =
      let forward statement_index before ({value; _} as statement : Statement.statement Node.t) =
        let _ = 
          match value with
          | Statement.Statement.Class {body; _ } -> 
            Some body
          | _ -> None
        in
        let statement_key = [%hash: int * int] (node_id, statement_index) in
        let after = State.forward ~statement_key before ~statement in
        Log.log
          ~section:`Fixpoint
          "\n%a\n  {  %a  }\n\n%a"
          State.pp
          before
          Statement.pp
          statement
          State.pp
          after;
        after
      in
      List.foldi ~f:forward ~init statements
    in
    compute_fixpoint
      cfg
      ~initial_index:Cfg.entry_index
      ~initial
      ~predecessors:Cfg.Node.predecessors
      ~successors:Cfg.Node.successors
      ~transition
      *)
  


  let backward ~cfg ~initial =
    let transition ~post_info:_ node_id init statements =
      let statement_index = ref (List.length statements) in
      let backward statement =
        statement_index := !statement_index - 1;
        let statement_key = [%hash: int * int] (node_id, !statement_index) in
        State.backward ~statement_key ~statement
      in
      List.fold_right ~f:backward ~init statements
    in
    our_compute_fixpoint
      cfg
      ~initial_index:Cfg.exit_index
      ~initial
      ~post_info:(Int.Map.empty)
      ~predecessors:Cfg.Node.successors
      ~successors:Cfg.Node.predecessors
      ~transition

end


module UsedefStruct = Make (UsedefState)