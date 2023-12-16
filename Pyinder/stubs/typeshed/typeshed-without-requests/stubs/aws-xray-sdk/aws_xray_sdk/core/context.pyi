import time
from logging import Logger
from typing import Any

from .. import global_sdk_config as global_sdk_config
from .exceptions.exceptions import SegmentNotFoundException as SegmentNotFoundException
from .models.dummy_entities import DummySegment as DummySegment
from .models.entity import Entity
from .models.segment import Segment
from .models.subsegment import Subsegment

log: Logger
SUPPORTED_CONTEXT_MISSING: Any
MISSING_SEGMENT_MSG: str
CXT_MISSING_STRATEGY_KEY: str

class Context:
    def __init__(self, context_missing: str = ...) -> None: ...
    def put_segment(self, segment: Segment) -> None: ...
    def end_segment(self, end_time: time.struct_time | None = ...) -> None: ...
    def put_subsegment(self, subsegment: Subsegment) -> None: ...
    def end_subsegment(self, end_time: time.struct_time | None = ...): ...
    def get_trace_entity(self): ...
    def set_trace_entity(self, trace_entity: Entity) -> None: ...
    def clear_trace_entities(self) -> None: ...
    def handle_context_missing(self) -> None: ...
    @property
    def context_missing(self): ...
    @context_missing.setter
    def context_missing(self, value: str) -> None: ...