# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# pyre-unsafe

from typing import Any, Tuple

color_names: Tuple[str, ...]

def colorize(text: str, opts: Any = ..., **kwargs) -> str: ...

make_style: Any = ...
