## Pull Request template

Please, fill in the following checklist when you submit a PR.  The
items you have done should be updated with a check mark (that is,
`[x]` instead of `[ ]`).

* General
   * [ ] Review the [CONTRIBUTING.md](../CONTRIBUTING.md) file for
         detailed contributing guidelines before sending a PR.
   * [ ] Your contribution is made under the project's [copyright
         license](../LICENSE-MIT).
   * [ ] Make sure that your PR is not a duplicate.
   * [ ] You have done your changes in a separate branch.
   * [ ] You have a descriptive commit message with a short title (first line).
   * [ ] You have only one commit.  If not, either squash them into one
         commit or contribute your change as a sequence of smaller Pull
         Requests.
* Basic sanity checks
   * [ ] You have run `runchecks.sh` and it said "Everything is OK".
* Testing and Documentation
   * [ ] Your changes include unit tests (if they are code changes).
   * [ ] If your change relates to the behaviour of the simulator, please
         include comments explaining which part of the [reference
         documentation](https://tx-2.github.io/documentation.html)
         describes the thing you're changing.
* If your change is a bugfix and it fully fixes an issue:
   * [ ] Put `closes #XXXX` in your pull request description to
         auto-close the issue that your PR fixes.

If any of the checklist items don't apply, please leave them
un-checked.

**PLEASE KEEP THE ABOVE IN YOUR PULL REQUEST.**
