module.exports = {
  root: true,
  parser: '@typescript-eslint/parser',
  parserOptions: {
      project: `./tsconfig.json`,
      "ecmaFeatures": {
          "jsx": true
      }
  },
  plugins: [
      '@typescript-eslint',
      'react',
      'sort-import'
  ],
  extends: [
      'plugin:react/jsx-runtime',
      'eslint:recommended',
      'plugin:react/recommended',
      'plugin:@typescript-eslint/recommended',
      'plugin:@typescript-eslint/recommended-requiring-type-checking'
  ],
  "rules": {
    "sort-imports": [
      "error",
      {
        "ignoreCase": true,
        "ignoreMemberSort": false,
      }
    ],
    // note you must disable the base rule as it can report incorrect errors
    "no-unused-vars": "off",
    "@typescript-eslint/no-unused-vars": [
    "warn", // or "error"
    {
      "argsIgnorePattern": "^_",
      "varsIgnorePattern": "^_",
      "caughtErrorsIgnorePattern": "^_"
    }
    ],

  },
  "settings": {
    "react": {
        "version": "detect"
    }
  }
};
