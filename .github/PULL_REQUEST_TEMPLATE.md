## Pull Request template

Please, fill in the following checklist when you submit a PR.

* [ ] Review the [CONTRIBUTING.md](../CONTRIBUTING.md) file for
      detailed contributing guidelines before sending a PR.
* [ ] Your contribution is made under the project's [copyright
      license](../LICENSE-MIT).
* [ ] Make sure that your PR is not a duplicate.
* [ ] You have done your changes in a separate branch.
* [ ] You have a descriptive commit message with a short title (first line).
* [ ] You have only one commit (if not, squash them into one commit).
* [ ] Your changes include unit tests (if they are code changes).
* [ ] `cargo test` passes.
* [ ] `cargo clippy` does not generate any warnings.
* [ ] Your code is formatted with `cargo fmt`.
* [ ] If your change is a bug-fix, put `closes #XXXX` in your commit
      message to auto-close the issue that your PR fixes.
* [ ] If your change relates to the behaviour of the simulator, please
      include comments explaining which part of the [reference
      documentation](https://tx-2.github.io/documentation.html)
      describes the thing you're changing.

**PLEASE KEEP THE ABOVE IN YOUR PULL REQUEST.**