(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

(**
 * This tool allows for marshaling directly over file descriptors (instead of
 * ocaml "channels") to avoid buffering so that we can safely use marshaling
 * and libancillary together.
 *
 * The problem:
   * Ocaml's marshaling is done over channels, which have their own internal
   * buffer. This means after reading a marshaled object from a channel, the
   * FD's position is not guaranteed to be pointing to the beginning of the
   * next marshaled object (but instead points to the position after the
   * buffered read). So another process cannot receive this FD (over
   * libancillary) to start reading the next object.
   *
 * The solution:
   * Start each message with a fixed-size preamble that describes the
   * size of the payload to read. Read precisely that many bytes directly
   * from the FD avoiding Ocaml channels entirely.
*)

exception Invalid_Int_Size_Exception
exception Payload_Size_Too_Large_Exception
exception Malformed_Preamble_Exception
exception Writing_Preamble_Exception
exception Writing_Payload_Exception
exception Reading_Preamble_Exception
exception Reading_Payload_Exception

(* We want to marshal exceptions (or at least their message+stacktrace) over  *)
(* the wire. This type ensures that no one will attempt to pattern-match on   *)
(* the thing we marshal: 'Values of extensible variant types, for example     *)
(* exceptions (of extensible type exn), returned by the unmarhsaller should   *)
(* not be pattern-matched over, because unmarshalling does not preserve the   *)
(* information required for matching their constructors.'                     *)
(* https://caml.inria.fr/pub/docs/manual-ocaml/libref/Marshal.html            *)
type remote_exception_data = {
  message : string;
  stack : string;
}

let preamble_start_sentinel = '\142'

(** Size in bytes. *)
let preamble_core_size = 4

let expected_preamble_size = preamble_core_size + 1

(** Payload size in bytes = 2^31 - 1. *)
let maximum_payload_size = (1 lsl (preamble_core_size * 8)) - 1

let get_preamble_core (size : int) =
  (* We limit payload size to 2^31 - 1 bytes. *)
  if size >= maximum_payload_size then
    raise Payload_Size_Too_Large_Exception;
  let rec loop i (remainder: int) acc =
    if i < 0 then acc
    else loop (i - 1) (remainder / 256)
        (Bytes.set acc i (Char.chr (remainder mod 256)); acc) in
  loop (preamble_core_size - 1) size (Bytes.create preamble_core_size)

let make_preamble (size : int) =
  let preamble_core = get_preamble_core size in
  let preamble = Bytes.create (preamble_core_size + 1) in
  Bytes.set preamble 0 preamble_start_sentinel;
  Bytes.blit preamble_core 0 preamble 1 4;
  preamble

let parse_preamble preamble =
  if (Bytes.length preamble) <> expected_preamble_size
  || (Bytes.get preamble 0) <> preamble_start_sentinel then
    raise Malformed_Preamble_Exception;
  let rec loop i acc =
    if i >= 5 then acc
    else loop (i + 1) ((acc * 256) + (int_of_char (Bytes.get preamble i))) in
  loop 1 0

let to_fd_with_preamble fd obj =
  let flag_list = [] in
  let payload = Marshal.to_bytes obj flag_list in
  let size = Bytes.length payload in
  let preamble = make_preamble size in
  let preamble_bytes_written =
    Unix.write fd preamble 0 expected_preamble_size in
  if preamble_bytes_written <> expected_preamble_size then
    raise Writing_Preamble_Exception;
  let bytes_written = Unix.write fd payload 0 size in
  if bytes_written <> size then
    raise Writing_Payload_Exception;
  ()

let rec read_payload fd buffer offset to_read =
  if to_read = 0 then offset else begin
    let bytes_read = Unix.read fd buffer offset to_read in
    if bytes_read = 0 then offset else begin
      read_payload fd buffer (offset+bytes_read) (to_read-bytes_read)
    end
  end

let from_fd_with_preamble fd =
  let preamble = Bytes.create expected_preamble_size in
  let bytes_read = Unix.read fd preamble 0 expected_preamble_size in
  if (bytes_read = 0)
  (* Unix manpage for read says 0 bytes read indicates end of file. *)
  then raise End_of_file
  else if (bytes_read <> expected_preamble_size) then
    (Printf.eprintf "Error, only read %d bytes for preamble.\n" bytes_read;
     raise Reading_Preamble_Exception);
  let payload_size = parse_preamble preamble in
  let payload = Bytes.create payload_size in
  let payload_size_read = read_payload fd payload 0 payload_size in
  if (payload_size_read <> payload_size) then
    raise Reading_Payload_Exception;
  Marshal.from_bytes payload 0
