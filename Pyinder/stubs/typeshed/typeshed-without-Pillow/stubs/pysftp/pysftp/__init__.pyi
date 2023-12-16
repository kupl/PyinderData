from _typeshed import Self
from contextlib import AbstractContextManager
from stat import S_IMODE as S_IMODE
from types import TracebackType
from typing import IO, Any, Callable, Sequence
from typing_extensions import Literal

import paramiko
from paramiko import AuthenticationException as AuthenticationException
from pysftp.exceptions import (
    ConnectionException as ConnectionException,
    CredentialException as CredentialException,
    HostKeysException as HostKeysException,
)
from pysftp.helpers import (
    WTCallbacks as WTCallbacks,
    _PathCallback,
    cd as cd,
    known_hosts as known_hosts,
    path_advance as path_advance,
    path_retreat as path_retreat,
    reparent as reparent,
    st_mode_to_int as st_mode_to_int,
    walktree as walktree,
)

class CnOpts:
    log: bool = ...
    compression: bool = ...
    ciphers: Sequence[str] | None = ...
    hostkeys: paramiko.HostKeys = ...
    def __init__(self, knownhosts: str | None = ...) -> None: ...
    def get_hostkey(self, host: str) -> paramiko.PKey: ...

_Callback = Callable[[int, int], Any]
_Path = str | bytes

class Connection:
    def __init__(
        self,
        host: str,
        username: str | None = ...,
        private_key: str | paramiko.RSAKey | paramiko.AgentKey | None = ...,
        password: str | None = ...,
        port: int = ...,
        private_key_pass: str | None = ...,
        ciphers: Sequence[str] | None = ...,
        log: bool = ...,
        cnopts: CnOpts | None = ...,
        default_path: _Path | None = ...,
    ) -> None: ...
    @property
    def pwd(self) -> str: ...
    def get(
        self, remotepath: _Path, localpath: _Path | None = ..., callback: _Callback | None = ..., preserve_mtime: bool = ...
    ) -> None: ...
    def get_d(self, remotedir: _Path, localdir: _Path, preserve_mtime: bool = ...) -> None: ...
    def get_r(self, remotedir: _Path, localdir: _Path, preserve_mtime: bool = ...) -> None: ...
    def getfo(self, remotepath: _Path, flo: IO[bytes], callback: _Callback | None = ...) -> int: ...
    def put(
        self,
        localpath: _Path,
        remotepath: _Path | None = ...,
        callback: _Callback | None = ...,
        confirm: bool = ...,
        preserve_mtime: bool = ...,
    ) -> paramiko.SFTPAttributes: ...
    def put_d(self, localpath: _Path, remotepath: _Path, confirm: bool = ..., preserve_mtime: bool = ...) -> None: ...
    def put_r(self, localpath: _Path, remotepath: _Path, confirm: bool = ..., preserve_mtime: bool = ...) -> None: ...
    def putfo(
        self,
        flo: IO[bytes],
        remotepath: _Path | None = ...,
        file_size: int = ...,
        callback: _Callback | None = ...,
        confirm: bool = ...,
    ) -> paramiko.SFTPAttributes: ...
    def execute(self, command: str) -> list[str]: ...
    def cd(self, remotepath: _Path | None = ...) -> AbstractContextManager[None]: ...  # noqa: F811
    def chdir(self, remotepath: _Path) -> None: ...
    def cwd(self, remotepath: _Path) -> None: ...
    def chmod(self, remotepath: _Path, mode: int = ...) -> None: ...
    def chown(self, remotepath: _Path, uid: int | None = ..., gid: int | None = ...) -> None: ...
    def getcwd(self) -> str: ...
    def listdir(self, remotepath: _Path = ...) -> list[str]: ...
    def listdir_attr(self, remotepath: _Path = ...) -> list[paramiko.SFTPAttributes]: ...
    def mkdir(self, remotepath: _Path, mode: int = ...) -> None: ...
    def normalize(self, remotepath: _Path) -> str: ...
    def isdir(self, remotepath: _Path) -> bool: ...
    def isfile(self, remotepath: _Path) -> bool: ...
    def makedirs(self, remotedir: _Path, mode: int = ...) -> None: ...
    def readlink(self, remotelink: _Path) -> str: ...
    def remove(self, remotefile: _Path) -> None: ...
    def unlink(self, remotefile: _Path) -> None: ...
    def rmdir(self, remotepath: _Path) -> None: ...
    def rename(self, remote_src: _Path, remote_dest: _Path) -> None: ...
    def stat(self, remotepath: _Path) -> paramiko.SFTPAttributes: ...
    def lstat(self, remotepath: _Path) -> paramiko.SFTPAttributes: ...
    def close(self) -> None: ...
    def open(self, remote_file: _Path, mode: str = ..., bufsize: int = ...) -> paramiko.SFTPFile: ...
    def exists(self, remotepath: _Path) -> bool: ...
    def lexists(self, remotepath: _Path) -> bool: ...
    def symlink(self, remote_src: _Path, remote_dest: _Path) -> None: ...
    def truncate(self, remotepath: _Path, size: int) -> int: ...
    def walktree(  # noqa: F811
        self, remotepath: _Path, fcallback: _PathCallback, dcallback: _PathCallback, ucallback: _PathCallback, recurse: bool = ...
    ) -> None: ...
    @property
    def sftp_client(self) -> paramiko.SFTPClient: ...
    @property
    def active_ciphers(self) -> tuple[str, str]: ...
    @property
    def active_compression(self) -> tuple[str, str]: ...
    @property
    def security_options(self) -> paramiko.SecurityOptions: ...
    @property
    def logfile(self) -> str | Literal[False]: ...
    @property
    def timeout(self) -> float | None: ...
    @timeout.setter
    def timeout(self, val: float | None) -> None: ...
    @property
    def remote_server_key(self) -> paramiko.PKey: ...
    def __del__(self) -> None: ...
    def __enter__(self: Self) -> Self: ...
    def __exit__(
        self, etype: type[BaseException] | None, value: BaseException | None, traceback: TracebackType | None
    ) -> None: ...
