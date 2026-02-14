"""
Output management — backward compatibility shim.

All real implementation lives in utils.log_lib. This module re-exports
the public API so existing code using `from utils.output import ...`
continues to work unchanged.

For new code, import directly from utils.log_lib:
    from utils.log_lib import OutputManager, init_output, get_output
"""

# Re-export everything from log_lib
from utils.log_lib.hints import (
    Hint,
    register_hint,
    register_hints,
    get_hint,
    get_hints_by_category,
    _HINTS,
)
from utils.log_lib.manager import (
    OutputManager,
    init_output,
    get_output,
    _manager,
)
