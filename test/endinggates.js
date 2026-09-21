'use strict';

// 结局必经抉择自检（node test/endinggates.js）
// 覆盖：
//   - 线性链全部选项必经；分叉合流点的必经选项与各支路非必经；
//   - 含环剧情的终止性（具体状态去重）：状态环上“必须先取再走”、结构环回边非必经；
//   - 多结局区域互不污染（岔向其他结局的边不参与必经判定）；
//   - 同场景多状态（终止死局状态 + 可继续状态）分别处理；
//   - 起点自身为终止态；不可达终止场景排除；死局 / 结局分类；
//     悬空 / 恒假 / 入口受阻选项不计入可走边；
//   - 必经次序 = 最短见证首次出现次序；见证路径每步状态与 UID；
//   - 非必经选项反例（绕开仍到达，found + 最短路径）与必经选项断言无解
//     （canAssertUnsolvable=true）；
//   - 状态上限截断 => 不下任何必经结论（endings=null）；起点前置受阻；
//   - 确定性（两次分析 JSON 完全一致）；非法参数 400；HTTP API。
const assert = require('assert');
const fs = require('fs');
const os = require('os');
const path = require('path');
const http = require('http');

// 隔离数据目录，避免污染开发数据；禁用播种（必须在加载项目模块之前设置）
const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'ending-gates-test-'));
process.env.DATA_DIR = tmpDir;
process.env.SEED_ON_START = 'false';

const { endingGates, endingCounterexample } = require('../src/endinggates');

let passed = 0;
const ok = (name, cond) => { assert.ok(cond, name); passed++; console.log(`  ✓ ${name}`); };
const gateOf = (r, sceneId) => r.endings.find((e) => e.sceneId === sceneId);
const optSeq = (p) => p.filter((n) => n.kind === 'option').map((n) => n.optionUid);
const sceneSeq = (p) => p.filter((n) => n.kind === 'scene').map((n) => n.sceneId);

// ---------- 线性链：每个选项都是必经 ----------
console.log('线性链（全部必经）：');
const chain = {
  startScene: 'a',
  scenes: [
    { id: 'a', title: 'A', options: [{ uid: 'o1', text: '去 b', target: 'b' }] },
    { id: 'b', title: 'B', options: [{ uid: 'o2', text: '去 c', target: 'c' }] },
    { id: 'c', title: 'C', options: [] },
  ],
};
const r1 = endingGates(chain);
ok('分析成功且完整（未截断）', r1.ok === true && r1.truncated === false);
ok('1 个可达终止场景 / 1 个终止状态', r1.counts.endings === 1 && r1.counts.endStates === 1);
const e1 = gateOf(r1, 'c');
ok('终局 c 为设计结局 ending', e1 && e1.kind === 'ending');
ok('两个选项全部必经', e1.gateCount === 2 && e1.gates.map((g) => g.uid).join(',') === 'o1,o2');
ok('必经次序按路径出现先后（o1 然后 o2）', e1.gates[0].order === 1 && e1.gates[1].order === 2);
ok('最短见证 2 步，场景序列 a,b,c', e1.depth === 2 && sceneSeq(e1.path).join(',') === 'a,b,c');
ok('见证路径每步带稳定 UID 与选择后状态',
  optSeq(e1.path).join(',') === 'o1,o2' &&
  e1.path.every((n) => (n.kind === 'scene' ? n.state : n.stateAfter) !== undefined));
ok('区域即全部 3 个节点，且没有非必经选项', e1.regionStates === 3 && e1.nonMandatoryCount === 0);

// ---------- 分叉：合流点选项必经，支路选项非必经 ----------
console.log('分叉合流（合流点必经）：');
const diamond = {
  startScene: 's',
  scenes: [
    { id: 's', options: [
      { uid: 'oa', text: '走 a', target: 'a' },
      { uid: 'ob', text: '走 b', target: 'b' }] },
    { id: 'a', options: [{ uid: 'oa2', text: 'a2', target: 'g' }] },
    { id: 'b', options: [{ uid: 'ob2', text: 'b2', target: 'g' }] },
    { id: 'g', options: [{ uid: 'og', text: '必经之门', target: 'end' }] },
    { id: 'end', options: [] },
  ],
};
const r2 = endingGates(diamond);
const e2 = gateOf(r2, 'end');
ok('只有合流点 og 必经', e2.gates.map((g) => g.uid).join(',') === 'og');
ok('两条支路的 4 个选项全部非必经',
  e2.nonMandatory.map((o) => o.uid).sort().join(',') === 'oa,oa2,ob,ob2');
// 反例：绕开支路选项 oa，仍能经 b 到达
const ce2a = endingCounterexample(diamond, { endingSceneId: 'end', uid: 'oa' });
ok('绕开 oa 的反例存在且只走 b 支路',
  ce2a.found === true && optSeq(ce2a.path).join(',') === 'ob,ob2,og');
// 反例：绕开合流点 og => 无解，可断言
const ce2b = endingCounterexample(diamond, { endingSceneId: 'end', uid: 'og' });
ok('绕开必经项 og 无解且可断言（canAssertUnsolvable）',
  ce2b.found === false && ce2b.canAssertUnsolvable === true && ce2b.path === null);

// ---------- 纯分叉（无合流）：没有任何必经选项 ----------
console.log('纯分叉（无共同选项）：');
const fork = {
  startScene: 's',
  scenes: [
    { id: 's', options: [
      { uid: 'pa', text: 'a', target: 'a' },
      { uid: 'pb', text: 'b', target: 'b' }] },
    { id: 'a', options: [{ uid: 'pa2', text: 'a2', target: 'end' }] },
    { id: 'b', options: [{ uid: 'pb2', text: 'b2', target: 'end' }] },
    { id: 'end', options: [] },
  ],
};
const r3 = endingGates(fork);
const e3 = gateOf(r3, 'end');
ok('两条路线无共同选项 => 0 个必经', e3.gateCount === 0);
ok('全部 4 个可走选项列为非必经', e3.nonMandatoryCount === 4);
const ce3 = endingCounterexample(fork, { endingSceneId: 'end', uid: 'pa' });
ok('绕开 pa 走 pb 支路到达', ce3.found === true && optSeq(ce3.path).join(',') === 'pb,pb2');

// ---------- 含状态环：必须先 take 翻转变量再 go ----------
console.log('含状态环（先取后走，take 与 go 都必经）：');
const stateLoop = {
  startScene: 's',
  variables: ['x'],
  scenes: [
    { id: 's', options: [
      { uid: 'take', text: '取得道具', condition: '!x', target: 's', assigns: [{ variable: 'x', value: true }] },
      { uid: 'go', text: '出发', condition: 'x', target: 'end' }] },
    { id: 'end', options: [] },
  ],
};
const r4 = endingGates(stateLoop);
ok('含环分析正常终止，具体状态去重为 3（s×2 + end）',
  r4.ok === true && r4.counts.states === 3);
const e4 = gateOf(r4, 'end');
ok('take 与 go 都是必经（不能直接 go，也不能只 take）',
  e4.gates.map((g) => g.uid).join(',') === 'take,go');
ok('最短见证 2 步：先 take 再 go', e4.depth === 2 && optSeq(e4.path).join(',') === 'take,go');
ok('见证路径中 s 的两个不同具体状态分别列出',
  e4.path.filter((n) => n.kind === 'scene' && n.sceneId === 's').length === 2);
const ce4 = endingCounterexample(stateLoop, { endingSceneId: 'end', uid: 'take' });
ok('绕开 take 永远无法满足 x => 无解可断言', ce4.found === false && ce4.canAssertUnsolvable === true);

// ---------- 含结构环：回边不是必经（可直接走，也可绕环） ----------
console.log('含结构环（回边非必经）：');
const structLoop = {
  startScene: 's',
  scenes: [
    { id: 's', options: [{ uid: 'a', text: '进入', target: 'm' }] },
    { id: 'm', options: [
      { uid: 'back', text: '折返', target: 's' },
      { uid: 'fwd', text: '继续', target: 'end' }] },
    { id: 'end', options: [] },
  ],
};
const r5 = endingGates(structLoop);
const e5 = gateOf(r5, 'end');
ok('回边 back 不是必经（可绕 0 圈）',
  e5.gates.map((g) => g.uid).join(',') === 'a,fwd' &&
  e5.nonMandatory.some((o) => o.uid === 'back'));
const ce5 = endingCounterexample(structLoop, { endingSceneId: 'end', uid: 'back' });
ok('绕开 back 的反例为直达路线 a -> fwd',
  ce5.found === true && optSeq(ce5.path).join(',') === 'a,fwd');
const ce5b = endingCounterexample(structLoop, { endingSceneId: 'end', uid: 'fwd' });
ok('绕开 fwd 只能在 s⇄m 间循环 => 无解可断言',
  ce5b.found === false && ce5b.canAssertUnsolvable === true);

// ---------- 陷阱循环选项对结局非必经 ----------
console.log('陷阱循环（困环选项非必经）：');
const trap = {
  startScene: 's',
  scenes: [
    { id: 's', options: [
      { uid: 'loop', text: '原地打转', target: 's' },
      { uid: 'finish', text: '结束', target: 'end' }] },
    { id: 'end', options: [] },
  ],
};
const r6 = endingGates(trap);
const e6 = gateOf(r6, 'end');
ok('只有 finish 必经，loop 非必经',
  e6.gates.map((g) => g.uid).join(',') === 'finish' &&
  e6.nonMandatory.some((o) => o.uid === 'loop'));
const ce6 = endingCounterexample(trap, { endingSceneId: 'end', uid: 'loop' });
ok('绕开 loop 直达 end', ce6.found === true && optSeq(ce6.path).join(',') === 'finish');

// ---------- 多结局：区域互不污染 ----------
console.log('多结局（区域隔离）：');
const twoEnds = {
  startScene: 's',
  scenes: [
    { id: 's', options: [{ uid: 'common', text: '共同前缀', target: 'fork' }] },
    { id: 'fork', options: [
      { uid: 'pa', text: 'A 线', target: 'endA' },
      { uid: 'pb', text: 'B 线', target: 'endB' }] },
    { id: 'endA', options: [] },
    { id: 'endB', options: [] },
  ],
};
const r7 = endingGates(twoEnds);
ok('两个结局分别给出', r7.endings.length === 2);
ok('endA 必经 common 与 pa（不含 pb）',
  gateOf(r7, 'endA').gates.map((g) => g.uid).join(',') === 'common,pa');
ok('endB 必经 common 与 pb（不含 pa）',
  gateOf(r7, 'endB').gates.map((g) => g.uid).join(',') === 'common,pb');
ok('endA 区域内不含 pb（岔向 endB 的边不污染）',
  !gateOf(r7, 'endA').nonMandatory.some((o) => o.uid === 'pb') &&
  gateOf(r7, 'endA').nonMandatoryCount === 0);
// 排序：深度相同按场景 ID（endA 在前）
ok('结局按最短见证深度、再按场景 ID 排序',
  r7.endings.map((e) => e.sceneId).join(',') === 'endA,endB');

// ---------- 同场景多状态：一个死局终止态 + 一个可继续态 ----------
console.log('同场景多状态（死局态与可继续态并存）：');
const multiState = {
  startScene: 's',
  variables: ['x'],
  scenes: [
    { id: 's', options: [
      { uid: 'u1', text: '带上 x', target: 'x', assigns: [{ variable: 'x', value: true }] },
      { uid: 'u2', text: '不带 x', target: 'x' }] },
    { id: 'x', options: [{ uid: 'ux', text: '需要 x', condition: 'x', target: 'realEnd' }] },
    { id: 'realEnd', options: [] },
  ],
};
const r8 = endingGates(multiState);
const dx = gateOf(r8, 'x');
const re = gateOf(r8, 'realEnd');
ok('x 为死局（deadend）且只有 1 个终止状态（x=false）',
  dx && dx.kind === 'deadend' && dx.states === 1);
ok('到达 x 死局的必经项只有 u2（不经 ux）', dx.gates.map((g) => g.uid).join(',') === 'u2');
ok('realEnd 必经 u1 与 ux（按序）', re.gates.map((g) => g.uid).join(',') === 'u1,ux');
ok('realEnd 最短见证 2 步', re.depth === 2 && optSeq(re.path).join(',') === 'u1,ux');
// 绕开 u1：只能 u2 -> x 死局，到不了 realEnd => 无解
const ce8 = endingCounterexample(multiState, { endingSceneId: 'realEnd', uid: 'u1' });
ok('绕开 u1 无法到达 realEnd（会落入 x 死局）', ce8.found === false && ce8.canAssertUnsolvable === true);

// ---------- 起点自身为终止态 ----------
console.log('起点即终止：');
const r9 = endingGates({ startScene: 'a', scenes: [{ id: 'a', options: [] }] });
ok('起点无选项 => 0 步设计结局，无必经项',
  r9.endings.length === 1 && r9.endings[0].kind === 'ending' &&
  r9.endings[0].depth === 0 && r9.endings[0].gateCount === 0 &&
  r9.endings[0].path.length === 1);

// ---------- 不可达终止场景不计入；悬空 / 恒假 / 入口受阻不可走 ----------
console.log('不可达与不可走选项：');
const r10 = endingGates({
  startScene: 'a',
  variables: ['x'],
  scenes: [
    { id: 'a', options: [
      { uid: 'good', text: '正常', target: 'b' },
      { uid: 'orphan', text: '悬空', target: 'nowhere' },
      { uid: 'false', text: '恒假', condition: 'neverSet', target: 'b' },
      { uid: 'blocked', text: '受阻', target: 'g' }] },
    { id: 'b', options: [] },
    { id: 'g', precondition: 'x', options: [{ uid: 'inside', text: '门内', target: 'b' }] },
    { id: 'iso', options: [] },
  ],
});
ok('只列出可达的 b 结局，孤岛 iso 排除',
  r10.endings.map((e) => e.sceneId).join(',') === 'b');
ok('悬空 / 恒假 / 入口受阻边不计入可走标签（labels 只含 good）',
  r10.counts.labels === 1 && r10.counts.transitions === 1);
const e10 = gateOf(r10, 'b');
ok('唯一可走边 good 必经', e10.gates.map((g) => g.uid).join(',') === 'good');

// 全部选项不可走 => 起点本身成为死局终止态
const r10b = endingGates({ startScene: 'a', variables: ['x'], scenes: [
  { id: 'a', options: [
    { uid: 'f', text: '恒假', condition: 'x', target: 'b' },
    { uid: 'o', text: '悬空', target: 'ghost' }] },
  { id: 'b', options: [] }] });
ok('全部不可走时起点为死局终止态',
  r10b.endings.length === 1 && r10b.endings[0].sceneId === 'a' &&
  r10b.endings[0].kind === 'deadend' && r10b.endings[0].gateCount === 0);

// ---------- 状态上限截断：不下任何必经结论 ----------
console.log('状态上限截断：');
const r11 = endingGates(chain, { maxStates: 1 });
ok('达到上限时 truncated 且 ok=false', r11.truncated === true && r11.ok === false);
ok('截断时 endings 为 null（不下必经结论）', r11.endings === null);
ok('截断说明文案明确', /不输出任何必经/.test(r11.message));
// 截断时反例也不能断言
const ce11 = endingCounterexample(chain, { endingSceneId: 'c', uid: 'o1' }, { maxStates: 1 });
ok('截断图上未找到反例时 canAssertUnsolvable=false',
  ce11.found === false && ce11.canAssertUnsolvable === false && ce11.truncated === true);

// ---------- 起点前置受阻 ----------
console.log('起点前置受阻：');
const r12 = endingGates({
  startScene: 'a', variables: ['k'],
  scenes: [
    { id: 'a', precondition: 'k', options: [{ uid: 'x', text: 'x', target: 'b' }] },
    { id: 'b', options: [] }],
});
ok('起点受阻：startBlocked 且无结局', r12.startBlocked === true && r12.endings.length === 0);

// ---------- 确定性 ----------
console.log('确定性：');
const demo = JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'samples', 'adventure-demo.json'), 'utf8'));
const d1 = endingGates(demo);
const d2 = endingGates(demo);
ok('同一剧情两次分析结果完全一致', JSON.stringify(d1) === JSON.stringify(d2));

// ---------- 示例剧情（含双死局结局、村庄/森林与城堡/女巫塔两处环） ----------
console.log('示例剧情：');
ok('示例：14 个具体状态、16 条可走边、9 个标签、2 个结局、3 个终止状态',
  d1.counts.states === 14 && d1.counts.transitions === 16 &&
  d1.counts.labels === 9 && d1.counts.endings === 2 && d1.counts.endStates === 3);
const castle = gateOf(d1, 'castle');
const ending = gateOf(d1, 'ending');
ok('两个结局均为死局（终章的选项指向不存在的巨龙场景；城堡存在全锁状态）',
  castle.kind === 'deadend' && ending.kind === 'deadend');
ok('终章必经 6 个选项（必先拿钥匙、回村、走官道、出示钥匙、登王座）',
  ending.gateCount === 6);
ok('终章最短见证 6 步且从 village 出发',
  ending.depth === 6 && ending.path[0].sceneId === 'village');
ok('城堡死局必经女巫往返链（官道->女巫塔->返回城堡）',
  castle.gates.map((g) => g.uid).join(',') === 'idx:village#1,idx:castle#2,idx:witchTower#0');
// 非必经项“前往女巫之塔”可绕开（走钥匙路线仍能到终章）
const ceD = endingCounterexample(demo, { endingSceneId: 'ending', uid: 'idx:castle#2' });
ok('绕开女巫塔选项仍能到达终章（钥匙路线反例）',
  ceD.found === true && !optSeq(ceD.path).includes('idx:castle#2'));
// 必经项“登上王座”不可绕开
const ceD2 = endingCounterexample(demo, { endingSceneId: 'ending', uid: 'idx:throneRoom#0' });
ok('绕开登王座无法到达终章，可断言必经',
  ceD2.found === false && ceD2.canAssertUnsolvable === true);

// ---------- 条件语法错误容错 ----------
const badCond = endingGates({
  startScene: 'a',
  scenes: [{ id: 'a', options: [{ uid: 'q1', text: 'x', condition: 'k &&', target: 'b' }] }, { id: 'b', options: [] }],
});
ok('语法错误条件按恒真处理并记录', badCond.counts.labels === 1 && badCond.conditionErrors.length === 1);

// ---------- 参数校验 ----------
const throws400 = (fn, re) => {
  try { fn(); } catch (e) { return e.status === 400 && re.test(e.message); }
  return false;
};
console.log('参数校验：');
ok('缺少起点 => 400', throws400(() => endingGates({ scenes: [{ id: 'a' }] }), /起点/));
ok('起点不存在 => 400', throws400(() => endingGates({ startScene: 'ghost', scenes: [{ id: 'a' }] }), /起点/));
ok('反例缺结局场景 => 400',
  throws400(() => endingCounterexample(chain, { uid: 'o1' }), /endingSceneId/));
ok('反例缺 UID => 400',
  throws400(() => endingCounterexample(chain, { endingSceneId: 'c' }), /UID/));
ok('反例结局场景不存在 => 400',
  throws400(() => endingCounterexample(chain, { endingSceneId: 'ghost', uid: 'o1' }), /不存在/));
ok('反例 UID 不存在 => 400',
  throws400(() => endingCounterexample(chain, { endingSceneId: 'c', uid: 'nope' }), /不存在/));

// ---------- HTTP API ----------
(async () => {
  console.log('HTTP API：');
  const app = require('../server');
  const server = app.listen(0, '127.0.0.1');
  await new Promise((resolve) => server.once('listening', resolve));
  const port = server.address().port;

  const req = (method, url, body) => new Promise((resolve, reject) => {
    const r = http.request({
      host: '127.0.0.1', port, path: url, method,
      headers: body !== undefined ? { 'Content-Type': 'application/json' } : undefined,
    }, (res) => {
      let data = '';
      res.on('data', (d) => { data += d; });
      res.on('end', () => {
        try { resolve({ status: res.statusCode, body: data ? JSON.parse(data) : null }); }
        catch (e) { reject(e); }
      });
    });
    r.on('error', reject);
    if (body !== undefined) r.write(JSON.stringify(body));
    r.end();
  });

  try {
    // 草稿分析（不落盘）
    const q1 = await req('POST', '/api/ending-gates', diamond);
    ok('POST /api/ending-gates 返回 200，合流点 og 必经',
      q1.status === 200 && q1.body.endings[0].gates.map((g) => g.uid).join(',') === 'og');

    // { story } 包装形式
    const q1b = await req('POST', '/api/ending-gates', { story: chain });
    ok('POST /api/ending-gates 接受 { story } 包装',
      q1b.status === 200 && q1b.body.endings[0].gateCount === 2);

    const q2 = await req('POST', '/api/ending-gates', { scenes: [{ id: 'a' }] });
    ok('缺少起点返回 400', q2.status === 400 && /起点/.test(q2.body.error || ''));

    // 反例接口
    const q3 = await req('POST', '/api/ending-gates/counterexample',
      { story: diamond, endingSceneId: 'end', uid: 'oa' });
    ok('反例接口 200 且找到绕开 oa 的路线',
      q3.status === 200 && q3.body.found === true &&
      q3.body.path.filter((n) => n.kind === 'option').map((n) => n.optionUid).join(',') === 'ob,ob2,og');
    const q3b = await req('POST', '/api/ending-gates/counterexample',
      { story: diamond, endingSceneId: 'end' });
    ok('反例接口缺 UID 返回 400', q3b.status === 400);

    // 已保存剧情接口
    const created = await req('POST', '/api/stories', diamond);
    ok('创建剧情成功', created.status === 201 && created.body.id);
    const sid = created.body.id;

    const q4 = await req('GET', `/api/stories/${sid}/ending-gates`);
    ok('GET /api/stories/:id/ending-gates 返回必经抉择',
      q4.status === 200 && q4.body.endings.length === 1 &&
      q4.body.endings[0].gateCount === 1 &&
      /^opt-/.test(q4.body.endings[0].gates[0].uid)); // 保存后选项带服务端分配的稳定 UID

    // 取保存后“合流门”选项的实际 UID（g 场景唯一选项）
    const saved = await req('GET', `/api/stories/${sid}`);
    const gateUid = saved.body.scenes.find((s) => s.id === 'g').options[0].uid;
    const q5 = await req('POST', `/api/stories/${sid}/ending-gates/counterexample`,
      { endingSceneId: 'end', uid: gateUid });
    ok('已保存剧情反例接口：绕开必经合流项无解可断言',
      q5.status === 200 && q5.body.found === false && q5.body.canAssertUnsolvable === true);

    const q6 = await req('GET', '/api/stories/no-such-id/ending-gates');
    ok('剧情不存在返回 404', q6.status === 404);
  } finally {
    server.close();
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }

  console.log(`\n全部 ${passed} 项结局必经抉择断言通过 ✔`);
})().catch((err) => {
  console.error(err);
  process.exit(1);
});
