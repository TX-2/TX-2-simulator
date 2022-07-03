import React, { useEffect, useRef } from 'react'

interface CanvasProps {
    className: string | undefined,
    draw: (context: CanvasRenderingContext2D) => void,
    id?: string,
}

const Canvas = ({ className, draw, id, ...rest }: CanvasProps) => {
    const canvasRef = useRef<HTMLCanvasElement>(null);

    useEffect(() => {
        const canvas = canvasRef.current
        if (canvas == null) {
            console.log("in Canvas useEffect callback, canvas ref is null.");
            return;
        }
        const context = canvas.getContext('2d');
        if (context == null) {
            console.log("in Canvas useEffect callback, rendering context is null.");
            return;
        } else {
            draw(context);
            return () => {
                // do nothing.
            };
        }
    }, [draw])
    console.log("rendering the canvas...");
    return <canvas ref={canvasRef} className={className} id={id} {...rest} />
}


interface KeyboardProps {
    className?: string | undefined,
    id?: string,
}

const Keyboard = (props: KeyboardProps) => {
    const draw = (ctx: CanvasRenderingContext2D) => {
        console.log("drawing the LW keyboard...");
        ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height)
        ctx.fillStyle = '#000000'
        ctx.beginPath()
        ctx.arc(50, 100, 20, 0, 2 * Math.PI)
        ctx.fill()
    }

    return <Canvas className={props.className} id={props.id} draw={draw} />
}

export default Keyboard;
