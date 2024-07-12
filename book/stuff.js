const json = (bmap) => {
  const map_P = null;
  const map_node = (lft) => (val) => (rgt) => ({
    type: 'node',
    left: json(lft),
    value: val(
      (v) => ({ type: 'some', value: v }),
      { type: 'none' }
    ),
    right: json(rgt)
  });
  const map_leaf = { type: 'leaf' };
  return BMap_match(null)(map_P)(map_node)(map_leaf)(bmap);
};
