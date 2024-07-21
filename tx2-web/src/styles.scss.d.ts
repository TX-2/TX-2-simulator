// Generated by @teamsupercell/typings-for-css-modules-loader
// Builds fail when this file is missing, which happens in CI pipelines; package.json just arranges for a second build which succeeds since the first creates this file.
declare namespace StylesScssNamespace {
  export interface IStylesScss {
    "alarm-panel": string;
    "alarm-panel__active": string;
    "alarm-panel__masked": string;
    "alarm-panel__message": string;
    "alarm-panel__name": string;
    gridbox: string;
    instructions: string;
    "io-panel": string;
    lw: string;
    lw__box: string;
    lw__cursor: string;
    "lw__cursor-animation": string;
    lw__input__keyboard: string;
    lw__input__keyboard_hits: string;
    lw__input__keyboard_keys: string;
    lw__output: string;
    lw__output_container: string;
    lw__paper: string;
    "main-grid-flexbox": string;
    "status-panel": string;
    "tape-load-modal__buttons": string;
  }
}

declare const StylesScssModule: StylesScssNamespace.IStylesScss & {
  /** WARNING: Only available when `css-loader` is used without `style-loader` or `mini-css-extract-plugin` */
  locals: StylesScssNamespace.IStylesScss;
};

export = StylesScssModule;
