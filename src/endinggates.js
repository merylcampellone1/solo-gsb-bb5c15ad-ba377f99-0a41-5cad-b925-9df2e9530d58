'use strict';

/**
 * 结局必经抉择（Ending Gates）
 *
 * 对每个**可达终止场景**，回答：“无论玩家怎么走，到达这个结局前都**必然**会经过
 * 哪些稳定选项（按 UID 标识）？按什么次序？首次到达的最短见证路线是什么？
 * 某个选项不是必经项时，给出一条绕开它仍能到达该结局的反例路线。”
 *
 * 图与分析器 / 路径查询 / 概率推演 / 覆盖路线相同：
 * 节点 = （场景 ID，全部布尔变量取值位图）的具体状态，按 场景ID+位图 去重，
 * 含环也必然终止；上限 MAX_STATES，超限即截断——截断时**不下任何必经结论**。
 *
 * 终止状态：某个具体状态没有任何“条件成立且目标可进入”的可走选项边（吸收态）。
 *   - 场景本身没有选项 => 设计结局（ending）；
 *   - 场景有选项但在该状态下全部不可走（恒假 / 悬空 / 入口受阻）=> 死局（deadend）。
 * 同一场景可以同时拥有终止状态与非终止状态（多状态），按状态分别处理。
 *
 * 必经判定（含环、不枚举固定深度路径）：
 *   对结局 E 的全部终止状态 T_E，先用反向 BFS 求出“能到达 T_E 的节点区域 R”
 *   （走向其他结局 / 陷阱循环的岔路不属于 R）。选项 UID 是边标签（同一选项在
 *   不同具体状态、在环上被多次走，标签相同）。
 *
 *   在有限图上求标签级的必经集合——对 R 内每个节点 v 定义
 *     M(v) = 从 v 出发的**每一条**最终停进 T_E 的路线都经过的标签集合
 *   （路线只在 R 内走，走到 R 外即不可能再到达 T_E，不算到达结局的路线）。
 *   递推（T_E 内节点 M = ∅）：
 *     M(v) = ⋂_{边 v --l--> w，w∈R} ( {l} ∪ M(w) )
 *   含环时这是单调方程组，取最大不动点（初值 M=全集，只删不增，迭代到稳定）。
 *   这是不动点闭包计算，不是固定深度路径枚举：环上节点参与迭代直到稳定，
 *   “绕环任意圈再出去”的全部路线都被涵盖（环只通向自身标签时该标签不会被
 *   误判为必经）。
 *
 *   起点的 M(s0) 即该结局的必经选项集合——它正好是“把带该标签的边全部删除后
 *   起点是否仍能到达 T_E”的割判据：非必经标签必然存在一条绕开它的到达路线，
 *   该路线由独立的 BFS 在同一张图上求出（最短反例）。
 *
 * 必经次序：取“首次到达该结局的最短见证路线”（BFS 树路径）上必经标签的首次
 * 出现次序。不同路线上次序可能交叉，UI 明确标注这是最短见证上的次序。
 */

const { compile } = require('./expression');
const { encodeState, decodeState, applyAssigns, collectStateVars, MAX_STATES } = require('./analyzer');

function badRequest(message) {
  return Object.assign(new Error(message), { status: 400 });
}

/**
 * 展开「场景 + 变量状态」具体状态图（与 probability / coverage 相同的语义与上限）。
 *
 * 返回：
 *   nodes: [{ sceneId, code, depth }]，下标即 BFS 发现顺序
 *   edges: [{ from, to, optKey, label, optionIndex, text, target, fromSceneId }]
 *   parents: nodeIndex -> { parent, edge }（起点为 null）
 *   labelOrder: [uid, ...] 可走边标签的首次出现顺序（同一 UID 只占一位）
 *   labelInfo:  uid -> { uid, sceneId, optionIndex, text, target }
 *   terminal:   Set<nodeIndex>（无可走出边的吸收态）
 *   terminalByScene: sceneId -> [nodeIndex, ...]（按节点下标，即 BFS 发现序）
 */
function expandGraph(storyInput, opts = {}) {
  const story = storyInput || {};
  const maxStates = Number.isInteger(opts.maxStates) && opts.maxStates > 0 ? opts.maxStates : MAX_STATES;

  const scenes = Array.isArray(story.scenes) ? story.scenes : [];
  const sceneMap = new Map();
  for (const s of scenes) {
    if (s && s.id && !sceneMap.has(s.id)) sceneMap.set(s.id, s);
  }
  if (!story.startScene || !sceneMap.has(story.startScene)) {
    throw badRequest('剧情缺少有效的起点场景，无法分析结局必经抉择');
  }

  // ---- 编译条件（语法错误按恒真处理，与其他模块一致） ----
  const conditionErrors = [];
  const safeCompile = (raw, where) => {
    try {
      return compile(raw);
    } catch (e) {
      conditionErrors.push({ where, message: e.message });
      return null;
    }
  };
  const sceneCond = new Map();
  const sceneAssigns = new Map();
  const optionCompiled = new Map(); // `${sceneId}#${idx}` -> { cond, assigns, option }
  let optionCount = 0;
  for (const scene of sceneMap.values()) {
    sceneCond.set(scene.id, safeCompile(scene.precondition, `场景 "${scene.id}" 的前置条件`));
    sceneAssigns.set(scene.id, (scene.assigns || []).filter((a) => a && a.variable));
    (scene.options || []).forEach((opt, idx) => {
      optionCount++;
      optionCompiled.set(`${scene.id}#${idx}`, {
        cond: safeCompile(opt && opt.condition, `场景 "${scene.id}" 选项 ${idx + 1} 的条件`),
        assigns: ((opt && opt.assigns) || []).filter((a) => a && a.variable),
        option: opt || {},
      });
    });
  }

  const knownVars = collectStateVars({ ...story, scenes });

  // UID -> 选项明细（稳定身份：优先 uid，旧数据退回 场景ID#下标，与覆盖路线一致）
  const labelInfo = new Map();
  for (const scene of sceneMap.values()) {
    (scene.options || []).forEach((opt, idx) => {
      const uid = (opt && opt.uid) || `idx:${scene.id}#${idx}`;
      if (!labelInfo.has(uid)) {
        labelInfo.set(uid, {
          uid,
          sceneId: scene.id,
          optionIndex: idx,
          text: (opt && opt.text) || '',
          target: ((opt && opt.target) || '').trim(),
        });
      }
    });
  }

  const startState = applyAssigns({}, sceneAssigns.get(story.startScene) || []);
  const startPc = sceneCond.get(story.startScene);
  const startBlocked = !!(startPc && !startPc.evaluate(startState));

  const nodes = [];
  const nodeIndex = new Map(); // `${sceneId}\x00${code}` -> index
  const edges = [];
  const outgoing = [];         // nodeIndex -> [edgeIndex, ...]
  const parents = [];
  const labelOrder = [];
  const labelBit = new Map();  // uid -> BigInt 位
  const queue = [];
  let truncated = false;

  const getOrCreate = (sceneId, code, depth, parentNode, edge) => {
    const key = `${sceneId}\x00${code}`;
    const hit = nodeIndex.get(key);
    if (hit !== undefined) return { idx: hit, created: false };
    const idx = nodes.length;
    nodes.push({ sceneId, code, depth });
    nodeIndex.set(key, idx);
    outgoing.push([]);
    parents.push(parentNode === null ? null : { parent: parentNode, edge });
    if (nodes.length > maxStates) { truncated = true; return { idx, created: true }; }
    queue.push(idx);
    return { idx, created: true };
  };

  const startNode = getOrCreate(
    story.startScene, encodeState(startState, knownVars), 0, null, null);
  const startIdx = startNode.idx;

  if (!startBlocked) {
    for (let head = 0; head < queue.length && !truncated; head++) {
      const cur = queue[head];
      const { sceneId, code } = nodes[cur];
      const scene = sceneMap.get(sceneId);
      const state = decodeState(code, knownVars);

      (scene.options || []).forEach((option, idx) => {
        if (truncated) return;
        const oc = optionCompiled.get(`${sceneId}#${idx}`);
        if (oc && oc.cond && !oc.cond.evaluate(state)) return; // 条件不成立：不可走
        const targetId = ((option && option.target) || '').trim();
        if (!targetId || !sceneMap.has(targetId)) return;      // 悬空跳转：不可走
        let nextState = state;
        if (oc && oc.assigns.length) nextState = applyAssigns(nextState, oc.assigns);
        nextState = applyAssigns(nextState, sceneAssigns.get(targetId) || []);
        const tc = sceneCond.get(targetId);
        if (tc && !tc.evaluate(nextState)) return;            // 入口前置不成立：不可走

        const label = (option && option.uid) || `idx:${sceneId}#${idx}`;
        let bit = labelBit.get(label);
        if (bit === undefined) {
          bit = 1n << BigInt(labelOrder.length);
          labelBit.set(label, bit);
          labelOrder.push(label);
        }
        const edgeInfo = {
          from: cur, label, bit,
          optKey: `${sceneId}#${idx}`,
          optionIndex: idx,
          text: (option && option.text) || '',
          target: targetId,
          fromSceneId: sceneId,
        };
        const made = getOrCreate(targetId, encodeState(nextState, knownVars),
          nodes[cur].depth + 1, cur, edgeInfo);
        if (truncated) return;
        const eIdx = edges.length;
        edgeInfo.to = made.idx;
        edges.push(edgeInfo);
        outgoing[cur].push(eIdx);
      });
    }
  }

  // 终止状态：没有任何可走出边的具体状态
  const terminal = new Set();
  const terminalByScene = new Map();
  if (!startBlocked) {
    for (let i = 0; i < nodes.length; i++) {
      if (outgoing[i].length === 0) {
        terminal.add(i);
        const sid = nodes[i].sceneId;
        if (!terminalByScene.has(sid)) terminalByScene.set(sid, []);
        terminalByScene.get(sid).push(i);
      }
    }
  }

  // 反向邻接（全局，供结局区域反向 BFS）
  const reverse = Array.from({ length: nodes.length }, () => []);
  edges.forEach((e, eIdx) => reverse[e.to].push(eIdx));
  // 前驱节点邻接（全局只建一次，供各结局不动点迭代复用）
  const predNodes = Array.from({ length: nodes.length }, () => []);
  for (const e of edges) predNodes[e.to].push(e.from);

  return {
    story, scenes, sceneMap, knownVars, conditionErrors, optionCount,
    nodes, edges, outgoing, reverse, predNodes, parents, labelOrder, labelBit, labelInfo,
    terminal, terminalByScene, truncated, startBlocked, maxStates,
    startSceneId: story.startScene,
  };
}

/** 由 BFS 父链重建场景 / 选项交替的完整路径（节点带状态，边带选择后状态） */
function buildWitnessPath(g, nodeIdx) {
  const trail = [];
  let cur = nodeIdx;
  while (cur !== null && cur !== undefined) {
    const node = g.nodes[cur];
    const sc = g.sceneMap.get(node.sceneId);
    trail.push({
      kind: 'scene', sceneId: node.sceneId,
      title: sc ? (sc.title || '') : '',
      state: decodeState(node.code, g.knownVars),
    });
    const p = g.parents[cur];
    if (!p || !p.edge) break;
    const e = p.edge;
    trail.push({
      kind: 'option',
      optionIndex: e.optionIndex,
      optionUid: e.label,
      optionText: e.text,
      fromSceneId: e.fromSceneId,
      target: e.target,
      stateAfter: decodeState(node.code, g.knownVars),
    });
    cur = p.parent;
  }
  trail.reverse();
  return trail;
}

/**
 * 单个结局的必经抉择计算。
 *
 * @param g     expandGraph 的结果
 * @param terminals 该结局场景的终止具体状态下标（按 BFS 发现序）
 * @returns { region:Set, must:bigint[], gates:bigint }
 */
function computeGates(g, terminals) {
  const n = g.nodes.length;
  const ALL = g.labelOrder.length ? (1n << BigInt(g.labelOrder.length)) - 1n : 0n;

  // ---- 反向 BFS：R = 能到达该结局某个终止状态的节点 ----
  const region = new Set(terminals);
  const rqueue = [...terminals];
  for (let head = 0; head < rqueue.length; head++) {
    const w = rqueue[head];
    for (const eIdx of g.reverse[w]) {
      const e = g.edges[eIdx];
      if (!region.has(e.from)) { region.add(e.from); rqueue.push(e.from); }
    }
  }

  const termSet = new Set(terminals);
  const must = new Array(n).fill(ALL);
  for (const t of terminals) must[t] = 0n;

  // ---- 最大不动点迭代（worklist）：
  //   M(v) = ⋀_{v--l-->w, w∈R} (bit(l) | M(w))，单调下降到稳定 ----
  // 前驱邻接在展图时全局建好（g.predNodes），这里各结局区域筛选复用，
  // 不随结局数重复 O(边数) 建表。
  const inList = new Uint8Array(n);
  const work = [];
  // 终止状态无出边；其余 R 内节点入列
  for (const v of region) {
    if (!termSet.has(v)) { work.push(v); inList[v] = 1; }
  }

  while (work.length) {
    const v = work.shift();
    inList[v] = 0;
    let acc = ALL;
    let hasEdge = false;
    for (const eIdx of g.outgoing[v]) {
      const e = g.edges[eIdx];
      if (!region.has(e.to)) continue; // 走不到该结局的岔路不参与
      hasEdge = true;
      acc &= (e.bit | must[e.to]);
      if (acc === 0n) break;
    }
    if (!hasEdge) acc = 0n; // 防御：R 内非终止节点必有通向 R 的边
    if (acc !== must[v]) {
      must[v] = acc;
      for (const u of g.predNodes[v]) {
        if (!inList[u] && region.has(u) && !termSet.has(u)) {
          inList[u] = 1;
          work.push(u);
        }
      }
    }
  }

  return { region, must, gates: must[0], ALL };
}

/** 必经标签在见证路线上的首次出现次序 */
function orderedGatesOnPath(g, path, gateBits) {
  const ordered = [];
  const seen = new Set();
  for (const node of path) {
    if (node.kind !== 'option') continue;
    const bit = g.labelBit.get(node.optionUid);
    if (bit === undefined) continue;
    if ((gateBits & bit) && !seen.has(node.optionUid)) {
      seen.add(node.optionUid);
      ordered.push(node.optionUid);
    }
  }
  return ordered;
}

const describeLabel = (g, uid, extra = {}) => ({ ...(g.labelInfo.get(uid) || { uid }), ...extra });

/**
 * 分析全部可达终止场景的必经抉择。
 *
 * @param storyInput 剧情对象（编辑中的草稿或已保存剧情）
 * @param opts       { maxStates } 测试可注入更小的状态上限
 */
function endingGates(storyInput, opts = {}) {
  const g = expandGraph(storyInput, opts);
  const counts = {
    states: g.nodes.length,
    transitions: g.edges.length,
    options: g.optionCount,
    labels: g.labelOrder.length,
    variables: g.knownVars.length,
    endStates: g.terminal.size,
    endings: g.terminalByScene.size,
  };

  if (g.startBlocked) {
    return {
      ok: true,
      truncated: false,
      startBlocked: true,
      startScene: g.startSceneId,
      counts,
      endings: [],
      knownVars: g.knownVars,
      conditionErrors: g.conditionErrors,
      statesExplored: g.nodes.length,
      maxStates: g.maxStates,
      message: '起点场景的前置条件在初始状态下不成立，剧情无法开始，没有任何可达的终止场景。',
    };
  }

  if (g.truncated) {
    // 状态图未展开完：未探索区域可能存在终止场景与绕路，不能下任何必经结论
    return {
      ok: false,
      truncated: true,
      startBlocked: false,
      startScene: g.startSceneId,
      counts,
      endings: null,
      knownVars: g.knownVars,
      conditionErrors: g.conditionErrors,
      statesExplored: g.nodes.length,
      maxStates: g.maxStates,
      message: `具体状态数量超过安全上限（${g.maxStates}），分析截断；未探索区域可能还有结局与绕路，`
        + '为避免以偏概全，本次不输出任何必经抉择结论。请减少变量数量后重试。',
    };
  }

  // ---- 逐结局计算必经抉择 ----
  const endings = [];
  for (const [sceneId, termNodes] of g.terminalByScene) {
    const scene = g.sceneMap.get(sceneId);
    const kind = (scene.options || []).length === 0 ? 'ending' : 'deadend';
    const firstTerminal = termNodes[0]; // 节点下标 = BFS 发现序，首个即最短见证
    const { region, must, gates: gateBits } = computeGates(g, termNodes);

    const path = buildWitnessPath(g, firstTerminal);
    const finalState = decodeState(g.nodes[firstTerminal].code, g.knownVars);
    const orderedUids = orderedGatesOnPath(g, path, gateBits);
    const gates = orderedUids.map((uid, i) => describeLabel(g, uid, { order: i + 1 }));

    // 非必经 = 在该结局区域 R 内的可走边标签中，不属于必经集合者（必然存在绕路）
    const gateSet = new Set(orderedUids);
    const nonMandatory = [];
    const seenNon = new Set();
    for (const e of g.edges) {
      if (!region.has(e.from) || !region.has(e.to)) continue;
      if (gateSet.has(e.label) || seenNon.has(e.label)) continue;
      seenNon.add(e.label);
      nonMandatory.push(describeLabel(g, e.label));
    }
    // 确定性：按标签在全图的首次出现顺序排列
    nonMandatory.sort((a, b) => g.labelOrder.indexOf(a.uid) - g.labelOrder.indexOf(b.uid));

    endings.push({
      sceneId,
      title: scene ? (scene.title || '') : '',
      kind,
      depth: g.nodes[firstTerminal].depth,
      states: termNodes.length,
      regionStates: region.size,
      gateCount: gates.length,
      gates,
      nonMandatoryCount: nonMandatory.length,
      nonMandatory,
      path,
      finalState,
    });
  }

  // 确定性排序：最短见证深度升序，再按场景 ID
  endings.sort((a, b) => (a.depth - b.depth) || a.sceneId.localeCompare(b.sceneId));

  const gateTotal = endings.reduce((acc, e) => acc + e.gateCount, 0);
  const message = `已穷举全部 ${counts.states} 个可达具体状态：`
    + `${endings.length} 个可达终止场景（${counts.endStates} 个终止状态），`
    + `共 ${gateTotal} 个结局必经选项`
    + (endings.every((e) => e.gateCount === 0)
      ? '；每个结局都存在不经过任何共同选项的多条到达路线（无必经抉择）'
      : '');

  return {
    ok: true,
    truncated: false,
    startBlocked: false,
    startScene: g.startSceneId,
    counts,
    endings,
    knownVars: g.knownVars,
    conditionErrors: g.conditionErrors,
    statesExplored: g.nodes.length,
    maxStates: g.maxStates,
    message,
  };
}

/**
 * 反例路线：绕开指定 UID 的选项后，是否仍能到达指定结局的某个终止状态。
 *
 * 在已展开的同一张具体状态图上做 BFS（图按状态去重，必然终止）：
 * 跳过所有带该标签的边，目标是该结局**原本的**终止状态集合；
 * 找到 => found:true + 最短反例路线；未找到且图完整 => 该选项确为必经
 * （canAssertUnsolvable:true）；图被截断 => 不能断言。
 *
 * @param storyInput 剧情对象
 * @param query      { endingSceneId, uid }
 * @param opts       { maxStates }
 */
function endingCounterexample(storyInput, queryInput = {}, opts = {}) {
  const query = queryInput || {};
  const endingSceneId = String(query.endingSceneId || '').trim();
  const uid = String(query.uid || '').trim();
  if (!endingSceneId) throw badRequest('缺少结局场景 endingSceneId');
  if (!uid) throw badRequest('缺少选项 UID uid');

  const g = expandGraph(storyInput, opts);
  if (!g.sceneMap.has(endingSceneId)) {
    throw badRequest(`结局场景 "${endingSceneId}" 不存在`);
  }
  if (!g.labelInfo.has(uid)) throw badRequest(`选项 UID "${uid}" 不存在`);
  const option = g.labelInfo.get(uid);

  const base = {
    endingSceneId,
    endingTitle: (g.sceneMap.get(endingSceneId) || {}).title || '',
    uid,
    option,
    startScene: g.startSceneId,
    statesExplored: g.nodes.length,
    maxStates: g.maxStates,
    truncated: g.truncated,
  };

  if (g.startBlocked) {
    return {
      ...base, ok: true, startBlocked: true, found: false,
      canAssertUnsolvable: false, path: null, depth: null, finalState: null,
      message: '起点场景的前置条件在初始状态下不成立，剧情无法开始。',
    };
  }

  const targetSet = new Set(g.terminalByScene.get(endingSceneId) || []);

  // BFS：跳过标签为 uid 的边
  const visited = new Uint8Array(g.nodes.length);
  const parentCE = new Array(g.nodes.length).fill(null); // node -> { parent, edge }
  const q = [0];
  visited[0] = 1;
  let goal = targetSet.has(0) ? 0 : -1;
  for (let head = 0; head < q.length && goal === -1; head++) {
    const v = q[head];
    for (const eIdx of g.outgoing[v]) {
      const e = g.edges[eIdx];
      if (e.label === uid) continue; // 绕开该选项
      if (visited[e.to]) continue;
      visited[e.to] = 1;
      parentCE[e.to] = { parent: v, edge: e };
      if (targetSet.has(e.to)) { goal = e.to; break; }
      q.push(e.to);
    }
  }

  if (goal !== -1) {
    // 用反例 BFS 的父链重建路径
    const trail = [];
    let cur = goal;
    while (cur !== null) {
      const node = g.nodes[cur];
      const sc = g.sceneMap.get(node.sceneId);
      trail.push({
        kind: 'scene', sceneId: node.sceneId,
        title: sc ? (sc.title || '') : '',
        state: decodeState(node.code, g.knownVars),
      });
      const p = parentCE[cur];
      if (!p) break;
      const e = p.edge;
      trail.push({
        kind: 'option',
        optionIndex: e.optionIndex,
        optionUid: e.label,
        optionText: e.text,
        fromSceneId: e.fromSceneId,
        target: e.target,
        stateAfter: decodeState(node.code, g.knownVars),
        avoided: false,
      });
      cur = p.parent;
    }
    trail.reverse();
    return {
      ...base, ok: true, startBlocked: false, found: true,
      canAssertUnsolvable: false,
      depth: g.nodes[goal].depth,
      path: trail,
      finalState: decodeState(g.nodes[goal].code, g.knownVars),
      message: `存在反例：绕开选项「${option.text || uid}」仍可到达结局「${endingSceneId}」`
        + `（最短 ${g.nodes[goal].depth} 步），因此该选项不是必经抉择。`,
    };
  }

  const canAssert = !g.truncated;
  return {
    ...base, ok: true, startBlocked: false, found: false,
    canAssertUnsolvable: canAssert,
    path: null, depth: null, finalState: null,
    message: g.truncated
      ? `状态图因上限被截断，未找到绕开「${option.text || uid}」到达该结局的路线；不能断言其是否必经`
      : (targetSet.size === 0
        ? `场景「${endingSceneId}」没有任何可达的终止状态，无法作为结局`
        : `绕开选项「${option.text || uid}」后不存在任何到达结局「${endingSceneId}」的路线`
          + '（已穷举全部可达状态，可断言该选项为必经抉择）'),
  };
}

module.exports = { endingGates, endingCounterexample, expandGraph };
