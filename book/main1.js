//./App/_.kind2//
//./Shape/_.kind2//
//./List/_.kind2//

const App = (S_1) => null;

const App_new = (S_1) => (tick_2) => (draw_3) => (when_4) => (P_5) => (new_6) =>
  new_6(tick_2)(draw_3)(when_4);

const Char = null;

const List = (T_1) => null;

const List_cons = (T_1) => (head_2) => (tail_3) => (P_4) => (cons_5) => (nil_6) =>
  cons_5(head_2)(tail_3);

const List_nil = (T_1) => (P_2) => (cons_3) => (nil_4) =>
  nil_4;

const Nat = null;

const Nat_succ = (n_1) => (P_2) => (succ_3) => (zero_4) =>
  succ_3(n_1);

const Nat_zero = (P_1) => (succ_2) => (zero_3) =>
  zero_3;

const Shape = null;

const Shape_circle = (pos_1) => (rad_2) => (P_3) => (line_4) => (circle_5) =>
  circle_5(pos_1)(rad_2);

const Shape_line = (ini_1) => (end_2) => (P_3) => (line_4) => (circle_5) =>
  line_4(ini_1)(end_2);

const String = List(Char);

const String_cons = (head_1) => (tail_2) => (P_3) => (cons_4) => (nil_5) =>
  cons_4(head_1)(tail_2);

const String_nil = (P_1) => (cons_2) => (nil_3) =>
  nil_3;

const V2 = null;

const V2_new = (x_1) => (y_2) => (P_3) => (new_4) =>
  new_4(x_1)(y_2);

const main = (() => {
  const tick_1 = (x__1) => 0;
  return (() => {
    const draw_2 = (state_2) =>
      List_cons(null)(Shape_circle(V2_new(100)(300))(12))(List_nil(null));
    return (() => {
      const when_3 = (state_3) => (event_4) => state_3;
      return App_new(null)(tick_1)(draw_2)(when_3);
    })();
  })();
})();

require("./rt.js");

// TASK: write a TypeScript type for App, Shape, etc.

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

// write a JavaScript function called fn_draw(canvas, shapes)
// that receives a canvas and an array of shapes (as a JSON)
// and draws every shape in the correct position in the canvas

// TODO: create a fn_when function that 


var MAIN = App_to_JSON(main);
var DRAW = MAIN.draw;

var shapes = List_to_JSON(Shape_to_JSON, DRAW(0));
//console.log(shapes);

window.onload = () => {
  console.log("->", shapes);

  var canvas = document.getElementById('canvas');
  fn_draw(canvas, shapes);
}
































