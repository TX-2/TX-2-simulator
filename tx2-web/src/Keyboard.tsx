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
  hdClass?: string | undefined,
  id?: string,
}

const Keyboard = (props: KeyboardProps) => {
    const draw = (ctx: CanvasRenderingContext2D, hitdetect: boolean) => {
        const painter = create_html_canvas_2d_painter(ctx, hitdetect);
        console.log("drawing the LW keyboard...");
        ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height)
        ctx.font = "24px sans-serif";
        draw_keyboard(painter)
    }
    const draw_vis = (ctx: CanvasRenderingContext2D) => {
        draw(ctx, false)
    }
    const draw_hitdetect = (ctx: CanvasRenderingContext2D) => {
        draw(ctx, true)
    }
  const w = 800;
  const h = 14.5 / 23.8 * w;
  // We draw two canvases; the first is visible and shows the actual
  // keyboard keys.  The second is invisible but the same size, and is
  // used for mouse pointer hit detection.
  return (<div>
    <Canvas
      className={props.className}
      id={props.id}
      draw={draw_vis}
      width={w}
      height={h}
    />
    <Canvas
      className={props.hdClass}
      id={props.id}
      draw={draw_hitdetect}
      width={w}
      height={h}
    />
  </div>);
}

export default Keyboard;
