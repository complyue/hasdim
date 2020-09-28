"""
Runtime data structures and routines

"""
__all__ = [
    "dtype",
    "float64",
    "f8",
    "float32",
    "f4",
    "int64",
    "i8",
    "int32",
    "i4",
    "int8",
    "byte",
    "intp",
    "yesno",
    "DbArray",
]

import asyncio
from typing import *

import os.path
import mmap
import numpy as np

from . import log

logger = log.get_logger(__name__)


class dtype:
    __slots__ = ("repr", "dt")

    def __init__(self, repr_: str, dt: Optional[np.dtype] = None):
        self.repr = repr_
        if dt is None:
            self.dt = np.dtype(repr_)
        else:
            self.dt = dt

    def __repr__(self):
        return self.repr


# align with builtin dtypes of hasdim
# fmt: off
float64 = dtype("float64") ; f8   = float64
float32 = dtype("float32") ; f4   = float32
int64   = dtype("int64")   ; i8   = int64
int32   = dtype("int32")   ; i4   = int32
int8    = dtype("int8")    ; byte = int8
intp    = dtype("intp")
yesno   = dtype('yesno', np.dtype("bool"))
# fmt: on


DbArrayHeaderDtype = np.dtype(
    [
        # version of array layout
        ("layout_version", "i4"),
        # a.k.a. padded header size
        ("data_offset", "i4"),
        # padded item size
        ("item_size", "i4"),
        # alignment required for an item
        ("item_align", "i4"),
        # number of valid items in the array, to be read/written on-the-fly
        # rest of the file content should be considered pre-allocated capacity
        ("data_length", "i8"),
    ],
    align=True,
)

# a disk file for array is always mmaped from beginning, data following the
# header. align the header so start of data is aligned with at least 512
# bits for possible SIMD performance improvement or even compliance
DbArrayHeaderAlign = 64

# so 40 bytes is unused in the head as far
DbArrayHeaderSize = DbArrayHeaderDtype.itemsize
assert DbArrayHeaderSize == 24, "C struct layout rules changed?"


def dbArrayHeaderV0(dtype_: dtype):
    dt = dtype_.dt
    hdr = np.ndarray(1, dtype=DbArrayHeaderDtype)
    hdr[0] = (
        0,
        DbArrayHeaderAlign * (1 + DbArrayHeaderSize // DbArrayHeaderAlign),
        dt.itemsize,
        dt.alignment,
        0,
    )
    return hdr


class DbArray:
    __slots__ = "data_dir", "data_path", "dtype", "mm", "hdr", "shape"

    def __init__(
        self,
        data_dir: str,
        data_path: str,
        dtype_: dtype = float64,
        shape: Optional[Tuple[int, ...]] = None,
    ):
        assert isinstance(dtype_, dtype)

        self.data_dir = data_dir
        self.data_path = data_path
        self.dtype = dtype_

        data_file_path = f"{data_dir}/{data_path}.dba"
        dt = dtype_.dt

        if shape is None:
            # load existing array file, use header and file length to
            # calculate shape, assuming 1d

            with open(data_file_path, "r+b") as f:
                fsz = f.seek(0, 2)
                if fsz < DbArrayHeaderSize:
                    # don't have a header long enough, most prolly not existing
                    # todo more care of abnormal situations
                    raise IOError(f"Invalid disk file for array: {data_file_path}")
                # existing and with a header long enough
                fd = f.fileno()
                self.mm = mmap.mmap(
                    fileno=fd,
                    length=0,
                    flags=mmap.MAP_SHARED,
                    access=mmap.ACCESS_WRITE,
                )
                self.hdr = np.ndarray(
                    shape=1, dtype=DbArrayHeaderDtype, buffer=self.mm, offset=0,
                )
            # caution: mm.size() is file size, not mmap'd size, don't misuse
            # memoryview(mm).nbytes is way to go otherwise
            fsz = self.mm.size()
            self.shape = ((fsz - self.hdr["data_offset"][0]) // dt.itemsize,)

        else:
            # create if not exists, or load existing file with truncation

            data_nbytes = dt.itemsize * np.prod(shape)

            data_file_dir = os.path.dirname(data_file_path)
            os.makedirs(data_file_dir, mode=0o755, exist_ok=True)
            fd = os.open(data_file_path, os.O_RDWR | os.O_CREAT, mode=0o644)
            try:
                hdrPayload = os.read(fd, DbArrayHeaderSize)
                if len(hdrPayload) == DbArrayHeaderSize:
                    # existing and with a header long enough

                    hdrRead = np.ndarray(
                        shape=1, dtype=DbArrayHeaderDtype, buffer=hdrPayload, offset=0,
                    )
                    expect_fsz = hdrRead["data_offset"][0] + data_nbytes
                    fsz = os.lseek(fd, 0, 2)
                    if fsz < expect_fsz:
                        os.ftruncate(fd, expect_fsz)
                    self.mm = mmap.mmap(
                        fileno=fd,
                        length=expect_fsz,
                        flags=mmap.MAP_SHARED,
                        access=mmap.ACCESS_WRITE,
                    )
                    self.hdr = np.ndarray(
                        shape=1, dtype=DbArrayHeaderDtype, buffer=self.mm, offset=0,
                    )

                else:
                    # don't have a header long enough, most prolly not existing
                    # todo more care for abnormal situations

                    hdr = dbArrayHeaderV0(dtype_)
                    expect_fsz = hdr["data_offset"][0] + data_nbytes
                    os.ftruncate(fd, expect_fsz)
                    self.mm = mmap.mmap(
                        fileno=fd,
                        length=expect_fsz,
                        flags=mmap.MAP_SHARED,
                        access=mmap.ACCESS_WRITE,
                    )
                    self.hdr = np.ndarray(
                        shape=1, dtype=DbArrayHeaderDtype, buffer=self.mm, offset=0,
                    )
                    self.hdr[:] = hdr

            finally:
                os.close(fd)

            try:
                self.shape = (int(shape),)
            except TypeError:
                self.shape = tuple(shape)

    def __repr__(self):
        return f"DbArray({self.data_dir!r},{self.data_path!r},dtype={self.dtype!r},shape={self.shape!r})"

    @property
    def len1d(self):
        return self.hdr["data_length"][0]

    @len1d.setter
    def len1d(self, len_: int):
        self.hdr["data_length"][0] = len_

    @property
    def ndarray(self):
        len1d = self.hdr["data_length"][0]
        return np.ndarray(
            shape=(len1d, *self.shape[1:]),
            dtype=self.dtype.dt,
            buffer=self.mm,
            offset=self.hdr["data_offset"][0],
        )

    @property
    def full_ndarray(self):
        return np.ndarray(
            shape=self.shape,
            dtype=self.dtype.dt,
            buffer=self.mm,
            offset=self.hdr["data_offset"][0],
        )

