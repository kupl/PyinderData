from _typeshed import Self
from typing import Any, Iterable, Iterator, Text

from .connections import Connection

class Cursor:
    connection: Connection[Any]
    description: tuple[Text, ...]
    rownumber: int
    rowcount: int
    arraysize: int
    messages: Any
    errorhandler: Any
    lastrowid: int
    def __init__(self, connection: Connection[Any]) -> None: ...
    def __del__(self) -> None: ...
    def close(self) -> None: ...
    def setinputsizes(self, *args) -> None: ...
    def setoutputsizes(self, *args) -> None: ...
    def nextset(self) -> bool | None: ...
    def mogrify(self, query: Text, args: object = ...) -> str: ...
    def execute(self, query: Text, args: object = ...) -> int: ...
    def executemany(self, query: Text, args: Iterable[object]) -> int | None: ...
    def callproc(self, procname: Text, args: Iterable[Any] = ...) -> Any: ...
    def scroll(self, value: int, mode: Text = ...) -> None: ...
    def __enter__(self: Self) -> Self: ...
    def __exit__(self, *exc_info: object) -> None: ...
    # Methods returning result tuples are below.
    def fetchone(self) -> tuple[Any, ...] | None: ...
    def fetchmany(self, size: int | None = ...) -> tuple[tuple[Any, ...], ...]: ...
    def fetchall(self) -> tuple[tuple[Any, ...], ...]: ...
    def __iter__(self) -> Iterator[tuple[Any, ...]]: ...

class DictCursorMixin:
    dict_type: Any  # TODO: add support if someone needs this
    def fetchone(self) -> dict[Text, Any] | None: ...
    def fetchmany(self, size: int | None = ...) -> tuple[dict[Text, Any], ...]: ...
    def fetchall(self) -> tuple[dict[Text, Any], ...]: ...
    def __iter__(self) -> Iterator[dict[Text, Any]]: ...

class SSCursor(Cursor):
    def fetchall(self) -> list[tuple[Any, ...]]: ...  # type: ignore[override]
    def fetchall_unbuffered(self) -> Iterator[tuple[Any, ...]]: ...
    def scroll(self, value: int, mode: Text = ...) -> None: ...

class DictCursor(DictCursorMixin, Cursor): ...  # type: ignore[misc]

class SSDictCursor(DictCursorMixin, SSCursor):  # type: ignore[misc]
    def fetchall_unbuffered(self) -> Iterator[dict[Text, Any]]: ...  # type: ignore[override]