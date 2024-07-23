// type V2 = {
//   $: "new";
//   x: number;
//   y: number;
// };
// 
// type Shape =
//   | {$: "line"; ini: V2; end: V2; }
//   | {$: "circle"; pos: V2; rad: number; };
// 
// type List<T>
//   = { $: "cons"; head: T; tail: List<T>; }
//   | { $: "nil"; };
// 
// type App<S> = {
//   $: "new";
//   tick: (state: S) => S;
//   draw: (state: S) => List<Shape>;
//   when: (state: S) => (event: number) => S;
// };

V2_to_JSON = (v2) => {
  return v2(null)(x => y => ({ $: "new", x: x, y: y }));
};

Shape_to_JSON = (shape) => {
  return (shape(null)
    (ini => end => ({ $: "line", ini: V2_to_JSON(ini), end: V2_to_JSON(end) }))
    (pos => rad => ({ $: "circle", pos: V2_to_JSON(pos), rad: rad }))
    (x_ini => ({ $: "x_shape", x_ini: V2_to_JSON(x_ini) }))
  );
};

List_to_JSON = (map, list) => {
  const result = [];
  let current = list;
  while (true) {
    var is_nil = current(null)
      (head => tail => {
        result.push(map(head));
        current = tail;
        return false;
      })
      (true);
    if (is_nil) {
      break;
    }
  }
  return result;
};

App_to_JSON = (app) => {
  return app(null)(init => tick => draw => when => ({ $: "new", init, tick, draw, when }));
};

DRAW = (canvas, shapes) => {
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  shapes.forEach(shape => {

    switch (shape.$) {
      case 'x_shape':
        const XSIZE = 20;
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(shape.x_ini.x - XSIZE / 2, shape.x_ini.y - XSIZE);
        ctx.lineTo(shape.x_ini.x + XSIZE / 2, shape.x_ini.y + XSIZE);
        ctx.stroke();
        ctx.beginPath();
        ctx.moveTo(shape.x_ini.x + XSIZE / 2, shape.x_ini.y - XSIZE);
        ctx.lineTo(shape.x_ini.x - XSIZE / 2, shape.x_ini.y + XSIZE);
        ctx.stroke();
        break;
      case 'line':
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(shape.ini.x, shape.ini.y);
        ctx.lineTo(shape.end.x, shape.end.y);
        ctx.stroke();
        break;
      case 'circle':
        ctx.fillStyle = 'black';
        ctx.beginPath();
        ctx.arc(shape.pos.x, shape.pos.y, shape.rad, 0, 2 * Math.PI);
        ctx.stroke();
        break;
    }
  });
};

RENDER = () => {
  DRAW(CANVAS, List_to_JSON(Shape_to_JSON, APP.draw(STATE)));
}

if (typeof window !== "undefined") {
  window.onload = () => {
    CANVAS = document.getElementById('canvas');
    APP = App_to_JSON(main);
    STATE = APP.init;
    RENDER();
  };

  TICK = () => {
    STATE = APP.tick(STATE);
    RENDER();
  };
  setInterval(TICK, 1000 / 30);

  document.addEventListener('DOMContentLoaded', () => {

    document.getElementById('canvas').addEventListener('click', (event) => {
      const rect = canvas.getBoundingClientRect();

      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;

      STATE = APP.when(x)(y)(STATE);

      RENDER();

    });
  });



}
