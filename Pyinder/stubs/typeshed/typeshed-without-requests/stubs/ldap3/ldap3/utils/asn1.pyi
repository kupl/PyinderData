from typing import Any

# Enable when pyasn1 gets stubs:
# from pyasn1.codec.ber.encoder import AbstractItemEncoder, BooleanEncoder
AbstractItemEncoder = Any
BooleanEncoder = Any

CLASSES: Any

class LDAPBooleanEncoder(AbstractItemEncoder):
    supportIndefLenMode: bool
    # Requires pyasn1 > 0.3.7
    def encodeValue(self, value, asn1Spec, encodeFun, **options): ...

customTagMap: Any
customTypeMap: Any

def compute_ber_size(data): ...
def decode_message_fast(message): ...
def decode_sequence(message, start, stop, context_decoders: Any | None = ...): ...
def decode_integer(message, start, stop, context_decoders: Any | None = ...): ...
def decode_octet_string(message, start, stop, context_decoders: Any | None = ...): ...
def decode_boolean(message, start, stop, context_decoders: Any | None = ...): ...
def decode_bind_response(message, start, stop, context_decoders: Any | None = ...): ...
def decode_extended_response(message, start, stop, context_decoders: Any | None = ...): ...
def decode_intermediate_response(message, start, stop, context_decoders: Any | None = ...): ...
def decode_controls(message, start, stop, context_decoders: Any | None = ...): ...
def ldap_result_to_dict_fast(response): ...
def get_byte(x): ...
def get_bytes(x): ...

DECODERS: Any
BIND_RESPONSE_CONTEXT: Any
EXTENDED_RESPONSE_CONTEXT: Any
INTERMEDIATE_RESPONSE_CONTEXT: Any
LDAP_MESSAGE_CONTEXT: Any
CONTROLS_CONTEXT: Any
