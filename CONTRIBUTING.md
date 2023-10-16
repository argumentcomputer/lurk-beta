# Contributing to Lurk

We want to make contributing to this project as easy and transparent as possible.

## Pull Requests
If you want to contribute a bug fix or feature to lurk, here's how to proceed:

1. Fork the repo and create your branch from `master`.
2. If you've added code that should be tested, add tests.
3. If you've changed APIs, update the documentation.
4. Ensure the test suite passes.
5. Submit your pull-request, writing a clear description of its intended purpose, and linking any issues it addresses

## Pull Request reviews

The maintainers will review your pull request as soon as they can, and it can only be merged once it has at least one approval . The comments can be in several forms:

- 'Comment' usually indicates the reviewer doesn't yet commit to approving your code but has important remarks to contribute.
- 'Request Changes' means changes need to be made before the reviewer approves at all.
- 'Approve' can be of two forms depending on the exact nature of the comments:
    -  Approval with no restrictions, or non-blocking comments indicates this can be merged by a maintainer.
    -  Approval with explicitly marked blocking comments means: "I don't need to review this again, but I need you (and trust you) to fix these issues first."

## Merging a Pull-request

A pull-request must meet certain criteria before it can be merged.

1. If you are fine with a squash merge, your pull-request's final commit should have at least one approval from a reviewer, and from all maintainers listed in the .github/CODEOWNERS file for the touched code sections.
2. If you prefer a classic merge, the pull-request should meet the above conditions, and and it should be a fast-forward merge from master, which implies it must also be up-to-date.

**Warning:** An up-to-date, rebased branch is required for a fast-forward merge. This means that your branch should not contain any merge commits: while we do not object to `Merge` as a pull-request merge method, we prefer the pull-request's history to be linear. To achieve this, you can update your local branch with `git pull --rebase` (see [doc](https://www.git-scm.com/docs/git-pull)).

A maintainer will merge your pull-request (or their own) using one of the following methods:
1.  The [GitHub's merge queue](https://github.blog/changelog/2023-02-08-pull-request-merge-queue-public-beta/) with a squash merge strategy. This is the simplest workflow and always acceptable if you don't mind having a single commit.
2.  If your commit history is carefully cleaned to remove unnecessary commits and ensure that each retained commit is meaningful, a repo admin may use the 'Merge' strategy.

Please feel free to specify your preferred merge method in your PR summary.

The implemented workflow is represented below, with rounded corners and dotted lines automatically handled by Github's merge queue:
```mermaid
flowchart TD
    Review{Is *last commit* of PR reviewed by CODEOWNERS?} -->|Yes| Squash
    Review --> |No| GReview[Get fresh review]
    GReview --> Review

    Squash{Are you OK with Squash merge?} -->|Yes| MQueue(Merge queue)
    Squash --> |No| Update{Is PR Up to date?}

    Update --> |Yes| Merge[Get a maintainer to merge it for you!]
    Update --> |No| Rebase[Rebase & get fresh review]
    Rebase --> Review

    Merge --> |It worked| Celebrate
    Merge --> |Somebody pushed to master before maintainer| Rebase

    MQueue -.-> |PR squash-merges cleanly on master & passes CI| Celebrate
    MQueue -.-> |Github merge queue found squash-merge or CI issue| Rebase
```

**Note:** In exceptional cases, we may preserve some messy commit history if not doing so would lose too much important information and fully disentangling is too difficult. We expect this would rarely apply.

## Issues
We use GitHub issues to track public bugs. Please ensure your description is clear and has sufficient instructions to be able to reproduce the issue.

## For maintainers: Benchmarking

To trigger a benchmark:

1. Click on the Actions tab in the upper part of the Github UI
2. Click on the "Benchmarking" section of the left-hand bar
3. Click on the "Run workflow" pulldown button on the right
4. Select the branch you want to benchmark, and click on the green "Run workflow" button to benchmark.

Then, check the following link for the benchmark reports:

https://lurk-lab.github.io/lurk-rs/benchmarks/criterion/reports/

Ask a maintainer for a benchmark report if you can't find a recent one.

## License
By contributing to lurk-lang, you agree that your contributions will be licensed under both [MIT](https://opensource.org/licenses/MIT) and [Apache 2.0](http://www.apache.org/licenses/LICENSE-2.0) licenses.
