# GitHub Workflows

## Tokens

The `API_TOKEN_GITHUB_DEMO` token is used in the [WASM Build, Test,
Deploy](deploy-wasm.yml) workflow to deploy the web app to
https://tx-2.github.io/demo.

To refresh the token, visit the Settings page of your own GitHub
profile and select "Developer Setting" -> "Personal Access Tokens" ->
"Tokens (classic)".  Select the token and click the "Regenerate Token"
button.  Copy the generated token value.

To apply it to the project, visit the Project's settings page, select
"Secrets and Variables" -> "Actions".  Update the token of the same
name in the "Repository Secrets" page.
