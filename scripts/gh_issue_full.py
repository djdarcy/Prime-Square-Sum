#!/usr/bin/env python3
"""
GitHub Issue Full View - Display complete issue context including timeline events,
cross-references, commits, sub-issues, and all metadata.

Usage:
    python scripts/gh_issue_full.py 24
    python scripts/gh_issue_full.py 24 --json
    python scripts/gh_issue_full.py 24 --compact
    python scripts/gh_issue_full.py 24 --ascii    # Force ASCII mode (no emoji)

Note: On Windows, the script automatically attempts to enable UTF-8 (chcp 65001).
      If that fails or output is piped, it falls back to ASCII symbols.
"""

import argparse
import json
import subprocess
import sys
import os
from collections import defaultdict
from datetime import datetime

# Symbol sets for different terminal capabilities
SYMBOLS_UNICODE = {
    "open": "🟢",
    "closed": "🔴",
    "item_open": "⭕",
    "item_closed": "✅",
    "parent": "📁",
    "bullet": "•",
}

SYMBOLS_ASCII = {
    "open": "[OPEN]",
    "closed": "[CLOSED]",
    "item_open": "[ ]",
    "item_closed": "[x]",
    "parent": "[PARENT]",
    "bullet": "*",
}


def setup_windows_utf8() -> bool:
    """Attempt to enable UTF-8 on Windows console. Returns True if successful."""
    if sys.platform != "win32":
        return True  # Non-Windows assumed to support UTF-8

    try:
        # Try to set console code page to UTF-8
        result = subprocess.run(
            ["chcp", "65001"],
            capture_output=True,
            shell=True,  # chcp is a shell builtin
            timeout=5
        )
        if result.returncode == 0:
            # Also reconfigure stdout for UTF-8
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            return True
    except Exception:
        pass

    # Fallback: just try to reconfigure stdout
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        # Test if we can actually write a Unicode character
        sys.stdout.write('\u2713')  # checkmark
        sys.stdout.write('\b \b')   # erase it
        return True
    except Exception:
        pass

    return False


def detect_utf8_support(force_ascii: bool = False) -> dict:
    """Detect whether to use Unicode or ASCII symbols."""
    if force_ascii:
        return SYMBOLS_ASCII

    # If stdout is not a TTY (piped/redirected), prefer ASCII for safety
    if not sys.stdout.isatty():
        return SYMBOLS_ASCII

    # Try to enable UTF-8 on Windows
    if setup_windows_utf8():
        return SYMBOLS_UNICODE

    return SYMBOLS_ASCII


# Global symbol set - will be initialized in main()
SYMBOLS = SYMBOLS_ASCII  # Safe default until main() runs


def run_gh(args: list[str]) -> dict | list | None:
    """Run a gh command and return parsed JSON output."""
    try:
        result = subprocess.run(
            ["gh"] + args,
            capture_output=True,
            text=True,
            encoding='utf-8',  # Explicit UTF-8 for Windows compatibility
            errors='replace',  # Replace undecodable chars instead of crashing
            check=True
        )
        return json.loads(result.stdout) if result.stdout.strip() else None
    except subprocess.CalledProcessError as e:
        print(f"Error running gh {' '.join(args)}: {e.stderr}", file=sys.stderr)
        return None
    except json.JSONDecodeError:
        return None


def get_issue_basic(issue_num: int, repo: str = None) -> dict | None:
    """Get basic issue information."""
    cmd = ["issue", "view", str(issue_num),
           "--json", "number,title,state,body,author,labels,assignees,milestone,createdAt,closedAt,comments"]
    if repo:
        cmd.extend(["--repo", repo])
    return run_gh(cmd)


def get_issue_timeline(owner: str, repo: str, issue_num: int) -> list | None:
    """Get issue timeline events."""
    return run_gh([
        "api", f"repos/{owner}/{repo}/issues/{issue_num}/timeline",
        "--paginate"
    ])


def get_sub_issues(owner: str, repo: str, issue_num: int) -> dict | None:
    """Get sub-issues via GraphQL."""
    query = f'''
    query {{
        repository(owner: "{owner}", name: "{repo}") {{
            issue(number: {issue_num}) {{
                parent {{ number title state }}
                subIssuesSummary {{ total completed percentCompleted }}
                subIssues(first: 50) {{
                    nodes {{ number title state }}
                }}
            }}
        }}
    }}
    '''
    return run_gh([
        "api", "graphql",
        "-H", "GraphQL-Features: sub_issues",
        "-f", f"query={query}"
    ])


def get_repo_info() -> tuple[str, str] | None:
    """Get current repo owner and name."""
    result = run_gh(["repo", "view", "--json", "owner,name"])
    if result:
        return result["owner"]["login"], result["name"]
    return None


def format_date(date_str: str | None) -> str:
    """Format ISO date to readable format."""
    if not date_str:
        return "N/A"
    try:
        dt = datetime.fromisoformat(date_str.replace("Z", "+00:00"))
        return dt.strftime("%Y-%m-%d %H:%M")
    except:
        return date_str


def process_timeline(timeline: list) -> dict:
    """Process timeline into categorized events."""
    events = defaultdict(list)

    for item in timeline:
        event_type = item.get("event")

        if event_type == "cross-referenced":
            source = item.get("source", {}).get("issue", {})
            if source:
                events["cross_references"].append({
                    "number": source.get("number"),
                    "title": source.get("title"),
                    "state": source.get("state")
                })

        elif event_type == "referenced":
            commit_id = item.get("commit_id", "")[:7]
            if commit_id:
                events["commits"].append({
                    "sha": commit_id,
                    "url": item.get("commit_url", "")
                })

        elif event_type == "labeled":
            events["labels_added"].append(item.get("label", {}).get("name"))

        elif event_type == "unlabeled":
            events["labels_removed"].append(item.get("label", {}).get("name"))

        elif event_type == "renamed":
            rename = item.get("rename", {})
            events["renames"].append({
                "from": rename.get("from"),
                "to": rename.get("to")
            })

        elif event_type == "assigned":
            assignee = item.get("assignee", {})
            events["assigned"].append(assignee.get("login"))

        elif event_type == "closed":
            events["closed"].append({
                "by": item.get("actor", {}).get("login"),
                "commit": item.get("commit_id", "")[:7] if item.get("commit_id") else None
            })

        elif event_type == "reopened":
            events["reopened"].append(item.get("actor", {}).get("login"))

        elif event_type == "commented":
            events["comment_count"] = events.get("comment_count", 0) + 1

        elif event_type in ("sub_issue_added", "sub_issue_removed"):
            # Sub-issues handled separately via GraphQL
            pass

    return dict(events)


def print_section(title: str, content: str = "", items: list = None):
    """Print a formatted section."""
    print(f"\n{'=' * 60}")
    print(f"  {title}")
    print('=' * 60)
    if content:
        print(content)
    if items:
        for item in items:
            print(f"  {item}")


def display_issue(issue_num: int, repo: str = None, output_json: bool = False, compact: bool = False):
    """Display full issue information."""

    # Get repo info - use explicit repo if provided, otherwise auto-detect
    if repo:
        if "/" not in repo:
            print(f"Error: --repo must be in owner/name format, got: {repo}", file=sys.stderr)
            sys.exit(1)
        owner, repo_name = repo.split("/", 1)
    else:
        repo_info = get_repo_info()
        if not repo_info:
            print("Error: Could not determine repository. Use --repo owner/name or run from within a git repo.", file=sys.stderr)
            sys.exit(1)
        owner, repo_name = repo_info

    # Fetch all data
    basic = get_issue_basic(issue_num, f"{owner}/{repo_name}" if repo else None)
    if not basic:
        print(f"Error: Could not fetch issue #{issue_num}", file=sys.stderr)
        sys.exit(1)

    timeline = get_issue_timeline(owner, repo_name, issue_num) or []
    sub_issues_data = get_sub_issues(owner, repo_name, issue_num)

    # Process timeline
    events = process_timeline(timeline)

    # Process sub-issues
    sub_issues = []
    parent = None
    sub_summary = None
    if sub_issues_data and "data" in sub_issues_data:
        issue_data = sub_issues_data["data"]["repository"]["issue"]
        if issue_data:
            parent = issue_data.get("parent")
            sub_summary = issue_data.get("subIssuesSummary")
            sub_issues = issue_data.get("subIssues", {}).get("nodes", [])

    # Build complete data structure
    full_data = {
        "basic": basic,
        "timeline_events": events,
        "sub_issues": sub_issues,
        "sub_issues_summary": sub_summary,
        "parent": parent,
        "repo": {"owner": owner, "name": repo_name}
    }

    if output_json:
        print(json.dumps(full_data, indent=2))
        return

    # Display formatted output
    state_icon = SYMBOLS["open"] if basic["state"] == "OPEN" else SYMBOLS["closed"]
    print(f"\n{state_icon} #{basic['number']}: {basic['title']}")
    print(f"   State: {basic['state']} | Author: {basic['author']['login']}")
    print(f"   Created: {format_date(basic['createdAt'])}")
    if basic.get("closedAt"):
        print(f"   Closed: {format_date(basic['closedAt'])}")

    # Labels
    if basic.get("labels"):
        labels = [f"[{l['name']}]" for l in basic["labels"]]
        print(f"   Labels: {' '.join(labels)}")

    # Assignees
    if basic.get("assignees"):
        assignees = [a["login"] for a in basic["assignees"]]
        print(f"   Assignees: {', '.join(assignees)}")

    # Milestone
    if basic.get("milestone"):
        print(f"   Milestone: {basic['milestone']['title']}")

    # Parent issue
    if parent:
        print(f"\n{SYMBOLS['parent']} PARENT ISSUE: #{parent['number']} - {parent['title']} ({parent['state']})")

    # Sub-issues
    if sub_issues:
        print_section(f"SUB-ISSUES ({sub_summary['completed']}/{sub_summary['total']} complete, {sub_summary['percentCompleted']:.0f}%)")
        for si in sub_issues:
            icon = SYMBOLS["item_closed"] if si["state"] == "CLOSED" else SYMBOLS["item_open"]
            print(f"  {icon} #{si['number']}: {si['title']}")

    # Cross-references
    if events.get("cross_references"):
        print_section("CROSS-REFERENCES (issues mentioning this)")
        seen = set()
        for ref in events["cross_references"]:
            if ref["number"] not in seen:
                seen.add(ref["number"])
                icon = SYMBOLS["item_closed"] if ref["state"] == "CLOSED" else SYMBOLS["item_open"]
                print(f"  {icon} #{ref['number']}: {ref['title']}")

    # Commits
    if events.get("commits"):
        print_section("COMMITS REFERENCING THIS ISSUE")
        for commit in events["commits"]:
            print(f"  {SYMBOLS['bullet']} {commit['sha']}")

    # Label history
    if events.get("labels_added") or events.get("labels_removed"):
        if not compact:
            print_section("LABEL HISTORY")
            if events.get("labels_added"):
                print(f"  Added: {', '.join(events['labels_added'])}")
            if events.get("labels_removed"):
                print(f"  Removed: {', '.join(events['labels_removed'])}")

    # Renames
    if events.get("renames") and not compact:
        print_section("TITLE CHANGES")
        for rename in events["renames"]:
            print(f"  \"{rename['from']}\"")
            print(f"  → \"{rename['to']}\"")

    # Body (truncated)
    if basic.get("body") and not compact:
        print_section("BODY (first 500 chars)")
        body = basic["body"][:500]
        if len(basic["body"]) > 500:
            body += "..."
        print(body)

    # Comments summary
    if basic.get("comments"):
        print_section(f"COMMENTS ({len(basic['comments'])} total)")
        for comment in basic["comments"][-3:]:  # Last 3 comments
            author = comment["author"]["login"]
            date = format_date(comment["createdAt"])
            preview = comment["body"][:100].replace("\n", " ")
            if len(comment["body"]) > 100:
                preview += "..."
            print(f"  [{date}] @{author}: {preview}")
        if len(basic["comments"]) > 3:
            print(f"  ... and {len(basic['comments']) - 3} earlier comments")

    print()


def main():
    global SYMBOLS

    parser = argparse.ArgumentParser(
        description="Display full GitHub issue context including timeline, cross-references, and sub-issues"
    )
    parser.add_argument("issue", type=int, help="Issue number")
    parser.add_argument("--repo", "-r", type=str, help="Repository in owner/name format (default: auto-detect from current directory)")
    parser.add_argument("--json", action="store_true", help="Output raw JSON")
    parser.add_argument("--compact", action="store_true", help="Compact output (skip body, label history, renames)")
    parser.add_argument("--ascii", action="store_true", help="Use ASCII symbols instead of Unicode/emoji (auto-detected if output is piped)")

    args = parser.parse_args()

    # Initialize symbol set based on terminal capabilities
    SYMBOLS = detect_utf8_support(force_ascii=args.ascii)

    display_issue(args.issue, repo=args.repo, output_json=args.json, compact=args.compact)


if __name__ == "__main__":
    main()
