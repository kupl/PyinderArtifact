import sys
from _collections_abc import dict_items, dict_keys, dict_values
from _typeshed import Self, SupportsKeysAndGetItem, SupportsRichComparison, SupportsRichComparisonT
from typing import Any, Generic, NoReturn, TypeVar, overload
from typing_extensions import SupportsIndex, final

if sys.version_info >= (3, 9):
    from types import GenericAlias

if sys.version_info >= (3, 10):
    from typing import Callable, Iterable, Iterator, Mapping, MutableMapping, MutableSequence, Reversible, Sequence
else:
    from _collections_abc import *

__all__ = ["ChainMap", "Counter", "OrderedDict", "UserDict", "UserList", "UserString", "defaultdict", "deque", "namedtuple"]

_S = TypeVar("_S")
_T = TypeVar("_T")
_T1 = TypeVar("_T1")
_T2 = TypeVar("_T2")
_KT = TypeVar("_KT")
_VT = TypeVar("_VT")
_KT_co = TypeVar("_KT_co", covariant=True)
_VT_co = TypeVar("_VT_co", covariant=True)

# namedtuple is special-cased in the type checker; the initializer is ignored.
if sys.version_info >= (3, 7):
    def namedtuple(
        typename: str,
        field_names: str | Iterable[str],
        *,
        rename: bool = ...,
        module: str | None = ...,
        defaults: Iterable[Any] | None = ...,
    ) -> type[tuple[Any, ...]]: ...

else:
    def namedtuple(
        typename: str, field_names: str | Iterable[str], *, verbose: bool = ..., rename: bool = ..., module: str | None = ...
    ) -> type[tuple[Any, ...]]: ...

class UserDict(MutableMapping[_KT, _VT], Generic[_KT, _VT]):
    data: dict[_KT, _VT]
    # __init__ should be kept roughly in line with `dict.__init__`, which has the same semantics
    @overload
    def __init__(self: UserDict[_KT, _VT], __dict: None = ...) -> None: ...
    @overload
    def __init__(self: UserDict[str, _VT], __dict: None = ..., **kwargs: _VT) -> None: ...
    @overload
    def __init__(self, __dict: SupportsKeysAndGetItem[_KT, _VT], **kwargs: _VT) -> None: ...
    @overload
    def __init__(self, __iterable: Iterable[tuple[_KT, _VT]], **kwargs: _VT) -> None: ...
    @overload
    def __init__(self: UserDict[str, str], __iterable: Iterable[list[str]]) -> None: ...
    def __len__(self) -> int: ...
    def __getitem__(self, key: _KT) -> _VT: ...
    def __setitem__(self, key: _KT, item: _VT) -> None: ...
    def __delitem__(self, key: _KT) -> None: ...
    def __iter__(self) -> Iterator[_KT]: ...
    def __contains__(self, key: object) -> bool: ...
    def copy(self: Self) -> Self: ...
    if sys.version_info >= (3, 7):
        def __copy__(self: Self) -> Self: ...

    # `UserDict.fromkeys` has the same semantics as `dict.fromkeys`, so should be kept in line with `dict.fromkeys`.
    # TODO: Much like `dict.fromkeys`, the true signature of `UserDict.fromkeys` is inexpressible in the current type system.
    # See #3800 & https://github.com/python/typing/issues/548#issuecomment-683336963.
    @classmethod
    @overload
    def fromkeys(cls, iterable: Iterable[_T], value: None = ...) -> UserDict[_T, Any | None]: ...
    @classmethod
    @overload
    def fromkeys(cls, iterable: Iterable[_T], value: _S) -> UserDict[_T, _S]: ...
    if sys.version_info >= (3, 9):
        def __or__(self, other: UserDict[_T1, _T2] | dict[_T1, _T2]) -> UserDict[_KT | _T1, _VT | _T2]: ...
        def __ror__(self, other: UserDict[_T1, _T2] | dict[_T1, _T2]) -> UserDict[_KT | _T1, _VT | _T2]: ...  # type: ignore[misc]
        # UserDict.__ior__ should be kept roughly in line with MutableMapping.update()
        @overload  # type: ignore[misc]
        def __ior__(self: Self, other: SupportsKeysAndGetItem[_KT, _VT]) -> Self: ...
        @overload
        def __ior__(self: Self, other: Iterable[tuple[_KT, _VT]]) -> Self: ...

class UserList(MutableSequence[_T]):
    data: list[_T]
    def __init__(self, initlist: Iterable[_T] | None = ...) -> None: ...
    def __lt__(self, other: list[_T] | UserList[_T]) -> bool: ...
    def __le__(self, other: list[_T] | UserList[_T]) -> bool: ...
    def __gt__(self, other: list[_T] | UserList[_T]) -> bool: ...
    def __ge__(self, other: list[_T] | UserList[_T]) -> bool: ...
    def __eq__(self, other: object) -> bool: ...
    def __contains__(self, item: object) -> bool: ...
    def __len__(self) -> int: ...
    @overload
    def __getitem__(self, i: SupportsIndex) -> _T: ...
    @overload
    def __getitem__(self: Self, i: slice) -> Self: ...
    @overload
    def __setitem__(self, i: SupportsIndex, item: _T) -> None: ...
    @overload
    def __setitem__(self, i: slice, item: Iterable[_T]) -> None: ...
    def __delitem__(self, i: SupportsIndex | slice) -> None: ...
    def __add__(self: Self, other: Iterable[_T]) -> Self: ...
    def __radd__(self: Self, other: Iterable[_T]) -> Self: ...
    def __iadd__(self: Self, other: Iterable[_T]) -> Self: ...
    def __mul__(self: Self, n: int) -> Self: ...
    def __rmul__(self: Self, n: int) -> Self: ...
    def __imul__(self: Self, n: int) -> Self: ...
    def append(self, item: _T) -> None: ...
    def insert(self, i: int, item: _T) -> None: ...
    def pop(self, i: int = ...) -> _T: ...
    def remove(self, item: _T) -> None: ...
    def copy(self: Self) -> Self: ...
    if sys.version_info >= (3, 7):
        def __copy__(self: Self) -> Self: ...

    def count(self, item: _T) -> int: ...
    # All arguments are passed to `list.index` at runtime, so the signature should be kept in line with `list.index`.
    def index(self, item: _T, __start: SupportsIndex = ..., __stop: SupportsIndex = ...) -> int: ...
    # All arguments are passed to `list.sort` at runtime, so the signature should be kept in line with `list.sort`.
    @overload
    def sort(self: UserList[SupportsRichComparisonT], *, key: None = ..., reverse: bool = ...) -> None: ...
    @overload
    def sort(self, *, key: Callable[[_T], SupportsRichComparison], reverse: bool = ...) -> None: ...
    def extend(self, other: Iterable[_T]) -> None: ...

class UserString(Sequence[UserString]):
    data: str
    def __init__(self, seq: object) -> None: ...
    def __int__(self) -> int: ...
    def __float__(self) -> float: ...
    def __complex__(self) -> complex: ...
    def __getnewargs__(self) -> tuple[str]: ...
    def __lt__(self, string: str | UserString) -> bool: ...
    def __le__(self, string: str | UserString) -> bool: ...
    def __gt__(self, string: str | UserString) -> bool: ...
    def __ge__(self, string: str | UserString) -> bool: ...
    def __eq__(self, string: object) -> bool: ...
    def __contains__(self, char: object) -> bool: ...
    def __len__(self) -> int: ...
    def __getitem__(self: Self, index: SupportsIndex | slice) -> Self: ...
    def __iter__(self: Self) -> Iterator[Self]: ...
    def __reversed__(self: Self) -> Iterator[Self]: ...
    def __add__(self: Self, other: object) -> Self: ...
    def __radd__(self: Self, other: object) -> Self: ...
    def __mul__(self: Self, n: int) -> Self: ...
    def __rmul__(self: Self, n: int) -> Self: ...
    def __mod__(self: Self, args: Any) -> Self: ...
    if sys.version_info >= (3, 8):
        def __rmod__(self: Self, template: object) -> Self: ...
    else:
        def __rmod__(self: Self, format: Any) -> Self: ...

    def capitalize(self: Self) -> Self: ...
    def casefold(self: Self) -> Self: ...
    def center(self: Self, width: int, *args: Any) -> Self: ...
    def count(self, sub: str | UserString, start: int = ..., end: int = ...) -> int: ...
    if sys.version_info >= (3, 8):
        def encode(self: UserString, encoding: str | None = ..., errors: str | None = ...) -> bytes: ...
    else:
        def encode(self: Self, encoding: str | None = ..., errors: str | None = ...) -> Self: ...

    def endswith(self, suffix: str | tuple[str, ...], start: int | None = ..., end: int | None = ...) -> bool: ...
    def expandtabs(self: Self, tabsize: int = ...) -> Self: ...
    def find(self, sub: str | UserString, start: int = ..., end: int = ...) -> int: ...
    def format(self, *args: Any, **kwds: Any) -> str: ...
    def format_map(self, mapping: Mapping[str, Any]) -> str: ...
    def index(self, sub: str, start: int = ..., end: int = ...) -> int: ...
    def isalpha(self) -> bool: ...
    def isalnum(self) -> bool: ...
    def isdecimal(self) -> bool: ...
    def isdigit(self) -> bool: ...
    def isidentifier(self) -> bool: ...
    def islower(self) -> bool: ...
    def isnumeric(self) -> bool: ...
    def isprintable(self) -> bool: ...
    def isspace(self) -> bool: ...
    def istitle(self) -> bool: ...
    def isupper(self) -> bool: ...
    if sys.version_info >= (3, 7):
        def isascii(self) -> bool: ...

    def join(self, seq: Iterable[str]) -> str: ...
    def ljust(self: Self, width: int, *args: Any) -> Self: ...
    def lower(self: Self) -> Self: ...
    def lstrip(self: Self, chars: str | None = ...) -> Self: ...
    @staticmethod
    @overload
    def maketrans(x: dict[int, _T] | dict[str, _T] | dict[str | int, _T]) -> dict[int, _T]: ...
    @staticmethod
    @overload
    def maketrans(x: str, y: str, z: str = ...) -> dict[int, int | None]: ...
    def partition(self, sep: str) -> tuple[str, str, str]: ...
    if sys.version_info >= (3, 9):
        def removeprefix(self: Self, __prefix: str | UserString) -> Self: ...
        def removesuffix(self: Self, __suffix: str | UserString) -> Self: ...

    def replace(self: Self, old: str | UserString, new: str | UserString, maxsplit: int = ...) -> Self: ...
    def rfind(self, sub: str | UserString, start: int = ..., end: int = ...) -> int: ...
    def rindex(self, sub: str | UserString, start: int = ..., end: int = ...) -> int: ...
    def rjust(self: Self, width: int, *args: Any) -> Self: ...
    def rpartition(self, sep: str) -> tuple[str, str, str]: ...
    def rstrip(self: Self, chars: str | None = ...) -> Self: ...
    def split(self, sep: str | None = ..., maxsplit: int = ...) -> list[str]: ...
    def rsplit(self, sep: str | None = ..., maxsplit: int = ...) -> list[str]: ...
    def splitlines(self, keepends: bool = ...) -> list[str]: ...
    def startswith(self, prefix: str | tuple[str, ...], start: int | None = ..., end: int | None = ...) -> bool: ...
    def strip(self: Self, chars: str | None = ...) -> Self: ...
    def swapcase(self: Self) -> Self: ...
    def title(self: Self) -> Self: ...
    def translate(self: Self, *args: Any) -> Self: ...
    def upper(self: Self) -> Self: ...
    def zfill(self: Self, width: int) -> Self: ...

class deque(MutableSequence[_T], Generic[_T]):
    @property
    def maxlen(self) -> int | None: ...
    def __init__(self, iterable: Iterable[_T] = ..., maxlen: int | None = ...) -> None: ...
    def append(self, __x: _T) -> None: ...
    def appendleft(self, __x: _T) -> None: ...
    def copy(self: Self) -> Self: ...
    def count(self, __x: _T) -> int: ...
    def extend(self, __iterable: Iterable[_T]) -> None: ...
    def extendleft(self, __iterable: Iterable[_T]) -> None: ...
    def insert(self, __i: int, __x: _T) -> None: ...
    def index(self, __x: _T, __start: int = ..., __stop: int = ...) -> int: ...
    def pop(self) -> _T: ...  # type: ignore[override]
    def popleft(self) -> _T: ...
    def remove(self, __value: _T) -> None: ...
    def rotate(self, __n: int = ...) -> None: ...
    def __copy__(self: Self) -> Self: ...
    def __len__(self) -> int: ...
    # These methods of deque don't take slices, unlike MutableSequence, hence the type: ignores
    def __getitem__(self, __index: SupportsIndex) -> _T: ...  # type: ignore[override]
    def __setitem__(self, __i: SupportsIndex, __x: _T) -> None: ...  # type: ignore[override]
    def __delitem__(self, __i: SupportsIndex) -> None: ...  # type: ignore[override]
    def __contains__(self, __o: object) -> bool: ...
    def __reduce__(self: Self) -> tuple[type[Self], tuple[()], None, Iterator[_T]]: ...
    def __iadd__(self: Self, __iterable: Iterable[_T]) -> Self: ...
    def __add__(self: Self, __other: Self) -> Self: ...
    def __mul__(self: Self, __other: int) -> Self: ...
    def __imul__(self: Self, __other: int) -> Self: ...
    def __lt__(self, __other: deque[_T]) -> bool: ...
    def __le__(self, __other: deque[_T]) -> bool: ...
    def __gt__(self, __other: deque[_T]) -> bool: ...
    def __ge__(self, __other: deque[_T]) -> bool: ...
    if sys.version_info >= (3, 9):
        def __class_getitem__(cls, __item: Any) -> GenericAlias: ...

class Counter(dict[_T, int], Generic[_T]):
    @overload
    def __init__(self: Counter[_T], __iterable: None = ...) -> None: ...
    @overload
    def __init__(self: Counter[str], __iterable: None = ..., **kwargs: int) -> None: ...
    @overload
    def __init__(self, __mapping: SupportsKeysAndGetItem[_T, int]) -> None: ...
    @overload
    def __init__(self, __iterable: Iterable[_T]) -> None: ...
    def copy(self: Self) -> Self: ...
    def elements(self) -> Iterator[_T]: ...
    def most_common(self, n: int | None = ...) -> list[tuple[_T, int]]: ...
    @classmethod
    def fromkeys(cls, iterable: Any, v: int | None = ...) -> NoReturn: ...  # type: ignore[override]
    @overload
    def subtract(self, __iterable: None = ...) -> None: ...
    @overload
    def subtract(self, __mapping: Mapping[_T, int]) -> None: ...
    @overload
    def subtract(self, __iterable: Iterable[_T]) -> None: ...
    # Unlike dict.update(), use Mapping instead of SupportsKeysAndGetItem for the first overload
    # (source code does an `isinstance(other, Mapping)` check)
    #
    # The second overload is also deliberately different to dict.update()
    # (if it were `Iterable[_T] | Iterable[tuple[_T, int]]`,
    # the tuples would be added as keys, breaking type safety)
    @overload  # type: ignore[override]
    def update(self, __m: Mapping[_T, int], **kwargs: int) -> None: ...
    @overload
    def update(self, __m: Iterable[_T], **kwargs: int) -> None: ...
    @overload
    def update(self, __m: None = ..., **kwargs: int) -> None: ...
    def __missing__(self, key: _T) -> int: ...
    def __delitem__(self, elem: object) -> None: ...
    if sys.version_info >= (3, 10):
        def __eq__(self, other: object) -> bool: ...
        def __ne__(self, other: object) -> bool: ...

    def __add__(self, other: Counter[_S]) -> Counter[_T | _S]: ...
    def __sub__(self, other: Counter[_T]) -> Counter[_T]: ...
    def __and__(self, other: Counter[_T]) -> Counter[_T]: ...
    def __or__(self, other: Counter[_S]) -> Counter[_T | _S]: ...  # type: ignore[override]
    def __pos__(self) -> Counter[_T]: ...
    def __neg__(self) -> Counter[_T]: ...
    # several type: ignores because __iadd__ is supposedly incompatible with __add__, etc.
    def __iadd__(self: Self, other: Counter[_T]) -> Self: ...  # type: ignore[misc]
    def __isub__(self: Self, other: Counter[_T]) -> Self: ...
    def __iand__(self: Self, other: Counter[_T]) -> Self: ...
    def __ior__(self: Self, other: Counter[_T]) -> Self: ...  # type: ignore[override,misc]
    if sys.version_info >= (3, 10):
        def total(self) -> int: ...
        def __le__(self, other: Counter[Any]) -> bool: ...
        def __lt__(self, other: Counter[Any]) -> bool: ...
        def __ge__(self, other: Counter[Any]) -> bool: ...
        def __gt__(self, other: Counter[Any]) -> bool: ...

@final
class _OrderedDictKeysView(dict_keys[_KT_co, _VT_co], Reversible[_KT_co]):  # type: ignore[misc]
    def __reversed__(self) -> Iterator[_KT_co]: ...

@final
class _OrderedDictItemsView(dict_items[_KT_co, _VT_co], Reversible[tuple[_KT_co, _VT_co]]):  # type: ignore[misc]
    def __reversed__(self) -> Iterator[tuple[_KT_co, _VT_co]]: ...

@final
class _OrderedDictValuesView(dict_values[_KT_co, _VT_co], Reversible[_VT_co], Generic[_KT_co, _VT_co]):  # type: ignore[misc]
    def __reversed__(self) -> Iterator[_VT_co]: ...

class OrderedDict(dict[_KT, _VT], Reversible[_KT], Generic[_KT, _VT]):
    def popitem(self, last: bool = ...) -> tuple[_KT, _VT]: ...
    def move_to_end(self, key: _KT, last: bool = ...) -> None: ...
    def copy(self: Self) -> Self: ...
    def __reversed__(self) -> Iterator[_KT]: ...
    def keys(self) -> _OrderedDictKeysView[_KT, _VT]: ...
    def items(self) -> _OrderedDictItemsView[_KT, _VT]: ...
    def values(self) -> _OrderedDictValuesView[_KT, _VT]: ...
    # The signature of OrderedDict.fromkeys should be kept in line with `dict.fromkeys`, modulo positional-only differences.
    # Like dict.fromkeys, its true signature is not expressible in the current type system.
    # See #3800 & https://github.com/python/typing/issues/548#issuecomment-683336963.
    @classmethod
    @overload
    def fromkeys(cls, iterable: Iterable[_T], value: None = ...) -> OrderedDict[_T, Any | None]: ...
    @classmethod
    @overload
    def fromkeys(cls, iterable: Iterable[_T], value: _S) -> OrderedDict[_T, _S]: ...
    # Keep OrderedDict.setdefault in line with MutableMapping.setdefault, modulo positional-only differences.
    @overload
    def setdefault(self: OrderedDict[_KT, _T | None], key: _KT) -> _T | None: ...
    @overload
    def setdefault(self, key: _KT, default: _VT) -> _VT: ...

class defaultdict(dict[_KT, _VT], Generic[_KT, _VT]):
    default_factory: Callable[[], _VT] | None
    @overload
    def __init__(self: defaultdict[_KT, _VT]) -> None: ...
    @overload
    def __init__(self: defaultdict[str, _VT], **kwargs: _VT) -> None: ...
    @overload
    def __init__(self, __default_factory: Callable[[], _VT] | None) -> None: ...
    @overload
    def __init__(self: defaultdict[str, _VT], __default_factory: Callable[[], _VT] | None, **kwargs: _VT) -> None: ...
    @overload
    def __init__(self, __default_factory: Callable[[], _VT] | None, __map: SupportsKeysAndGetItem[_KT, _VT]) -> None: ...
    @overload
    def __init__(
        self: defaultdict[str, _VT],
        __default_factory: Callable[[], _VT] | None,
        __map: SupportsKeysAndGetItem[str, _VT],
        **kwargs: _VT,
    ) -> None: ...
    @overload
    def __init__(self, __default_factory: Callable[[], _VT] | None, __iterable: Iterable[tuple[_KT, _VT]]) -> None: ...
    @overload
    def __init__(
        self: defaultdict[str, _VT],
        __default_factory: Callable[[], _VT] | None,
        __iterable: Iterable[tuple[str, _VT]],
        **kwargs: _VT,
    ) -> None: ...
    def __missing__(self, __key: _KT) -> _VT: ...
    def __copy__(self: Self) -> Self: ...
    def copy(self: Self) -> Self: ...

class ChainMap(MutableMapping[_KT, _VT], Generic[_KT, _VT]):
    maps: list[MutableMapping[_KT, _VT]]
    def __init__(self, *maps: MutableMapping[_KT, _VT]) -> None: ...
    def new_child(self: Self, m: MutableMapping[_KT, _VT] | None = ...) -> Self: ...
    @property
    def parents(self: Self) -> Self: ...
    def __setitem__(self, key: _KT, value: _VT) -> None: ...
    def __delitem__(self, key: _KT) -> None: ...
    def __getitem__(self, key: _KT) -> _VT: ...
    def __iter__(self) -> Iterator[_KT]: ...
    def __len__(self) -> int: ...
    def __contains__(self, key: object) -> bool: ...
    def __missing__(self, key: _KT) -> _VT: ...  # undocumented
    def __bool__(self) -> bool: ...
    def setdefault(self, key: _KT, default: _VT = ...) -> _VT: ...
    @overload
    def pop(self, key: _KT) -> _VT: ...
    @overload
    def pop(self, key: _KT, default: _VT | _T = ...) -> _VT | _T: ...
    def copy(self: Self) -> Self: ...
    __copy__ = copy
    # All arguments to `fromkeys` are passed to `dict.fromkeys` at runtime, so the signature should be kept in line with `dict.fromkeys`.
    @classmethod
    @overload
    def fromkeys(cls, iterable: Iterable[_T], __value: None = ...) -> ChainMap[_T, Any | None]: ...
    @classmethod
    @overload
    def fromkeys(cls, __iterable: Iterable[_T], __value: _S) -> ChainMap[_T, _S]: ...
    if sys.version_info >= (3, 9):
        def __or__(self, other: Mapping[_T1, _T2]) -> ChainMap[_KT | _T1, _VT | _T2]: ...
        def __ror__(self, other: Mapping[_T1, _T2]) -> ChainMap[_KT | _T1, _VT | _T2]: ...
        # ChainMap.__ior__ should be kept roughly in line with MutableMapping.update()
        @overload  # type: ignore[misc]
        def __ior__(self: Self, other: SupportsKeysAndGetItem[_KT, _VT]) -> Self: ...
        @overload
        def __ior__(self: Self, other: Iterable[tuple[_KT, _VT]]) -> Self: ...
