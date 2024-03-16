let _Char = 0;
let _List = (_T) => 0;
let _List_cons = (_head) => (_tail) => (_P) => (_cons) => (_nil) => ((_cons(_head))(_tail));
let _List_nil = (_P) => (_cons) => (_nil) => _nil;
let _Nat = 0;
let _Nat_succ = (_n) => (_P) => (_succ) => (_zero) => (_succ(_n));
let _Nat_zero = (_P) => (_succ) => (_zero) => _zero;
let _String = (_List(_Char));
let _String_cons = (_head) => (_tail) => (_P) => (_cons) => (_nil) => ((_cons(_head))(_tail));
let _String_nil = (_P) => (_cons) => (_nil) => _nil;
let _Tree = (_A) => 0;
let _Tree_fold = (_bm) => (_nd) => (_lf) => {
  let _bm_P = 0;
  let _bm_node = (_bm_val) => (_bm_lft) => (_bm_rgt) => (_nd) => (_lf) => (((_nd(_bm_val))(((_Tree_fold(_bm_lft))(_nd))(_lf)))(((_Tree_fold(_bm_rgt))(_nd))(_lf)));
  let _bm_leaf = (_nd) => (_lf) => _lf;
  return (((((_bm(_bm_P))(_bm_node))(_bm_leaf))(_nd))(_lf));
};
let _Tree_gen = (_n) => (_x) => {
  if (_n === 0) {
    return _Tree_leaf;
  } else {
    let _n_1 = _n - 1;
    return (((_Tree_node(_x))((_Tree_gen(_n_1))(((_x * 2) + 1))))((_Tree_gen(_n_1))(((_x * 2) + 2))));
  }
};
let _Tree_leaf = (_P) => (_node) => (_leaf) => _leaf;
let _Tree_node = (_val) => (_lft) => (_rgt) => (_P) => (_node) => (_leaf) => (((_node(_val))(_lft))(_rgt));
let _Tree_sum = (_x) => {
  let _x_P = 0;
  let _x_node = (_x_val) => (_x_lft) => (_x_rgt) => (_x_val + (_x_lft + _x_rgt));
  let _x_leaf = 0;
  return (((_Tree_fold(_x))(_x_node))(_x_leaf));
};
let __main = (_Tree_sum((_Tree_gen(22))(0)));

console.log(__main)
