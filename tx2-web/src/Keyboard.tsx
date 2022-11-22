import { create_html_canvas_2d_painter, draw_keyboard } from '../build/tx2_web'
import React, { useEffect, useRef, useState } from 'react'
import { Tx2Controller } from 'controller/tx2';

type Coordinates = {
    x: number;
    y: number;
};

interface CanvasProps {
  className: string | undefined,
  draw: (context: CanvasRenderingContext2D) => void,
  click: (
    event: React.MouseEvent<HTMLCanvasElement, MouseEvent>,
    canvas: HTMLCanvasElement) => void,
  width: number,
  height: number,
  willReadFrequently: boolean,
}

const getCoordinates = (ev: React.MouseEvent<HTMLCanvasElement, MouseEvent>, canvas: HTMLCanvasElement): Coordinates | undefined => {
  return {x: ev.pageX - canvas.offsetLeft, y: ev.pageY - canvas.offsetTop};
};

const Canvas = ({ className, draw, click, width, height, willReadFrequently, ...rest }: CanvasProps) => {
    const canvasRef = useRef<HTMLCanvasElement>(null);

    useEffect(() => {
        const canvas = canvasRef.current
        if (canvas == null) {
            console.log("in Canvas useEffect callback, canvas ref is null.");
            return;
        }
        const context = canvas.getContext('2d', { willReadFrequently: willReadFrequently});
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

  const doClick = (ev: React.MouseEvent<HTMLCanvasElement, MouseEvent>) => {
    if (!canvasRef.current) {
      return;
    }
    const canvas: HTMLCanvasElement = canvasRef.current;
    click(ev, canvas)
  }

  console.log("rendering the canvas...");
  return <canvas
    ref={canvasRef}
    className={className}
    width={width}
    height={height}
    onClick={doClick}
    {...rest} />
}

interface KeyboardProps {
  tx2Controller: Tx2Controller,
  className?: string | undefined,
  hdClass?: string | undefined,
  unit: number,
}

const Keyboard = (props: KeyboardProps) => {
    const [farActive, setFarActive] = useState(false);
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
    const click_hitdetect = (event: React.MouseEvent<HTMLCanvasElement, MouseEvent>, canvas: HTMLCanvasElement) => {
      // Not yet implemented.
      console.log("in Canvas click callback for hit detector canvas, it's not implemented.");
      console.log({event});
      const context = canvas.getContext('2d');
      if (!context) {
        return;
      }
      const clickPos = getCoordinates(event, canvas)
      if (!clickPos) {
        return;
      }
      const data = context.getImageData(clickPos.x, clickPos.y, 1, 1).data;
      console.log("RGB(A) value (on hit detector canvas) at click position is", data)
      if (data) {
        const result = props.tx2Controller.lwKeyPress(props.unit, farActive, data);
        setFarActive(result.far_keyboard_is_active)
        if (!result.consumed) {
          console.log("in Canvas click callback for hit detector canvas, input can't be accepted, perhaps the LW input unit is not connected.");
        }
      } else {
        console.log("in Canvas click callback for hit detector canvas, failed to get image data for hit position.");
      }
    }
    const click_keyboard = (_event: React.MouseEvent, _canvas: HTMLCanvasElement) => {
      // We don't need to do anything, the work is done in click_hitdetect.
    }
  const w = 800;
  const h = 14.5 / 23.8 * w;
  // We draw two canvases; the first is visible and shows the actual
  // keyboard keys.  The second is invisible but the same size, and is
  // used for mouse pointer hit detection.
  return (<div>
    <Canvas
      className={props.className}
      draw={draw_vis}
      click={click_keyboard}
      width={w}
      height={h}
      willReadFrequently={false}
    />
    <Canvas
      className={props.hdClass}
      draw={draw_hitdetect}
      click={click_hitdetect}
      width={w}
      height={h}
      willReadFrequently={true}
    />
  </div>);
}

export default Keyboard;
