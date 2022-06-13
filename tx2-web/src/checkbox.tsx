import React, { FC, ReactElement } from "react";

interface Props {
        isChecked: boolean;
        handleChange: (event: React.ChangeEvent<HTMLInputElement>) => void;
        label: string;
}

const Checkbox: FC<Props> = ({isChecked, handleChange, label}): ReactElement => {
        return (
                <div>
                        <label htmlFor={label}>{label}</label>
                        <input
                                type="checkbox"
                                id={label}
                                checked={isChecked}
                                onChange={handleChange}
                        />
                </div>
        );
};
export default Checkbox;
