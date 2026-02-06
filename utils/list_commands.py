"""
List command handlers for --list CATEGORY.

Provides display functions for functions, equations, algorithms, and config.
Extracted from prime-square-sum.py to keep the entry point focused on
argument parsing and expression evaluation.
"""

from utils.function_registry import FunctionRegistry
from utils.cli import (
    print_equations_list,
    load_equations_file,
    show_config,
)
from utils.sieve import (
    get_available_algorithms, get_algorithm_info,
    ALGORITHM_AUTO, ALGORITHM_PRIMESIEVE, ALGORITHM_BASIC,
    ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL,
)


def handle_list_functions(registry: FunctionRegistry) -> int:
    """List all available functions grouped by namespace."""
    signatures = registry.list_signatures()

    # Group by namespace
    groups: dict = {}
    for name, description in signatures.items():
        if '.' in name:
            ns = name.split('.')[0]
        else:
            ns = "(other)"
        groups.setdefault(ns, []).append(description)

    print("\nAvailable Functions:")
    print("=" * 60)

    # Display in priority order: user > pss > math
    namespace_order = ["user", "pss", "math"]
    for ns in namespace_order:
        if ns in groups:
            print(f"\n  [{ns}]")
            for desc in sorted(groups[ns]):
                print(f"    {desc}")
            del groups[ns]

    # Any remaining namespaces
    for ns, descs in sorted(groups.items()):
        print(f"\n  [{ns}]")
        for desc in sorted(descs):
            print(f"    {desc}")

    print()
    print("=" * 60)
    print(f"\nUnqualified names resolve by priority: user > pss > math")
    print(f"Total: {len(registry)} functions")
    return 0


def handle_list_algorithms() -> int:
    """List all available algorithm variants."""
    print("\nAvailable Algorithm Variants:")
    print("=" * 60)

    info = get_algorithm_info()

    # Group by class (currently only sieve)
    print("\nSieve Algorithms (--algorithm sieve:<variant>):")
    print("-" * 50)

    for algo in [ALGORITHM_AUTO, ALGORITHM_PRIMESIEVE, ALGORITHM_BASIC,
                 ALGORITHM_SEGMENTED, ALGORITHM_INDIVIDUAL]:
        algo_info = info.get(algo, {})
        status = "OK" if algo_info.get("available", False) else "NOT INSTALLED"
        desc = algo_info.get("description", "")
        time_c = algo_info.get("complexity_time", "")
        space_c = algo_info.get("complexity_space", "")

        print(f"  {algo:12} [{status}]")
        print(f"               {desc}")
        if time_c:
            print(f"               Time: {time_c}, Space: {space_c}")
        print()

    print("Usage:")
    print("  --algorithm sieve:auto        Auto-select best available")
    print("  --algorithm sieve:segmented   Force segmented (bounded memory)")
    print("  --algorithm sieve:basic       Force basic sieve")
    print("  --algorithm sieve:individual  Force individual testing")
    print()
    print("Resource preferences (--prefer):")
    print("  cpu      Prefer CPU-intensive algorithms")
    print("  memory   Prefer faster algorithms even if memory-heavy")
    print("  minimal  Prefer minimal memory usage")
    print("  gpu      Prefer GPU acceleration where available")

    return 0


def handle_list_equations(registry: FunctionRegistry) -> int:
    """List equations with compact function summary."""
    print_equations_list()
    # Show compact function summary for discoverability
    compact = registry.list_compact()
    ns_order = ["user", "pss", "math"]
    shown = [ns for ns in ns_order if ns in compact]
    shown += [ns for ns in sorted(compact) if ns not in ns_order]
    if shown:
        print("\nAvailable functions:")
        for ns in shown:
            names = compact[ns]
            line = ', '.join(names)
            if len(line) > 100:
                truncated = []
                length = 0
                for n in names:
                    addition = len(n) + (2 if truncated else 0)
                    if length + addition > 65:
                        break
                    truncated.append(n)
                    length += addition
                line = f"{', '.join(truncated)}, ... ({len(names)} total)"
            print(f"  {ns}: {line}")
        print("  Use --list functions for details.")
    return 0


def handle_list_menu(registry: FunctionRegistry) -> int:
    """Show available --list categories with counts."""
    equations = []
    try:
        eq_file = load_equations_file()
        if eq_file:
            equations = list(eq_file.equations.values())
    except Exception:
        pass

    algo_count = len(get_available_algorithms())

    print("\nAvailable categories for --list:")
    print()
    print(f"  equations    Saved equations from equations.json ({len(equations)} available)")
    print(f"  functions    Mathematical functions by namespace ({len(registry)} total)")
    print(f"  algorithms   Sieve algorithm variants ({algo_count} available)")
    print(f"  config       Effective configuration and defaults")
    print()
    print("Usage: --list CATEGORY  (e.g., --list functions)")
    print("       --list all       (show everything)")
    return 0


def handle_list(category: str, args, registry: FunctionRegistry) -> int:
    """Unified dispatch for --list CATEGORY."""
    if category == 'menu':
        return handle_list_menu(registry)

    # Display order for --list all (shorter/more common first)
    if category == 'all':
        categories = ['equations', 'functions', 'algorithms', 'config']
    else:
        categories = [category]

    handlers = {
        'equations': lambda: handle_list_equations(registry),
        'functions': lambda: handle_list_functions(registry),
        'algorithms': lambda: handle_list_algorithms(),
        'config': lambda: (show_config(), 0)[1],
    }

    for cat in categories:
        if cat in handlers:
            handlers[cat]()
            if category == 'all' and cat != categories[-1]:
                print()  # Separator between sections

    return 0
