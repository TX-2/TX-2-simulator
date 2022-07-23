import { create_html_canvas_2d_painter, draw_keyboard } from '../build/tx2_web'
import React, { useEffect, useRef } from 'react'

interface CanvasProps {
    className: string | undefined,
    draw: (context: CanvasRenderingContext2D) => void,
    id?: string,
  width: number,
  height: number,
}

const Canvas = ({ className, draw, id, width, height, ...rest }: CanvasProps) => {
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
  return <canvas
    ref={canvasRef}
    className={className}
    id={id}
    width={width}
    height={height}
    {...rest} />
}


interface KeyboardProps {
    className?: string | undefined,
    id?: string,
}

const Keyboard = (props: KeyboardProps) => {
    const draw = (ctx: CanvasRenderingContext2D) => {
        const painter = create_html_canvas_2d_painter(ctx);
        console.log("drawing the LW keyboard...");
        ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height)
        ctx.font = "24px sans-serif";
        draw_keyboard(painter)
    }
  const w = 800;
  const h = 14.5 / 23.8 * w;
  return (<Canvas
    className={props.className}
    id={props.id}
    draw={draw}
    width={w}
    height={h}
  />);
}

export default Keyboard;
