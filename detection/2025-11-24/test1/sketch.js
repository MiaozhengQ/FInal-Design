// ============ 全局变量 ============
let videoEl;
let pose;
let resultsForDraw = null;
let trail = [];
let selectedLandmark = 16;
const MAX_TRAIL = 200;
let playBtn;
let poseReady = false;
let pausedFreeze = false;

const LANDMARKS = [
  "nose","leftEyeInner","leftEye","leftEyeOuter","rightEyeInner","rightEye","rightEyeOuter",
  "leftEar","rightEar","mouthLeft","mouthRight","leftShoulder","rightShoulder","leftElbow","rightElbow",
  "leftWrist","rightWrist","leftPinky","rightPinky","leftIndex","rightIndex","leftThumb","rightThumb",
  "leftHip","rightHip","leftKnee","rightKnee","leftAnkle","rightAnkle","leftHeel","rightHeel","leftFootIndex","rightFootIndex"
];

const POSE_CONNECTIONS = [
  [11,13],[13,15],[12,14],[14,16],
  [11,12],[11,23],[12,24],[23,24],
  [23,25],[25,27],[24,26],[26,28],
  [27,29],[29,31],[28,30],[30,32],
  [15,17],[17,19],[19,21],[16,18],[18,20],[20,22],
  [0,1],[1,3],[0,2],[2,4],[5,6],[5,7],[6,8],[7,9],[8,10]
];

// 平滑相关
let smoothedLandmarks = null;
const SMOOTH_ALPHA_HIGH = 0.75;
const SMOOTH_ALPHA_LOW = 0.90;
const VISIBILITY_THRESHOLD = 0.35;
const TRAIL_MIN_DIST = 3;
const MAX_JUMP_PX = 60;
const HIST_LEN = 5;
const EWMA_ALPHA = 0.80;
let historyBuffers = null;

// 对齐相关
let puppetTemplate = null;
let boneLengths = null;
let mirrorForced = null;
let mirrorDecisionCounter = 0;
const MIRROR_SWITCH_COUNT = 5;
const MIRROR_ERROR_RATIO = 0.92;
let currentTransform = null;
const TRANSFORM_LERP = 0.4;
const ALIGN_INDICES = [0, 5, 6, 11, 12, 23, 24];

// 手动编辑相关
let manualEditMode = false;
let manualSelectedIdx = -1;
let manualHoverIndex = -1;
let manualDragging = false;
let enableAutoAlign = true;
let stableFrameCount = 0;
const STABLE_FRAMES_THRESHOLD = 15;

// ============ 辅助函数 ============
function copyLandmarks(src) {
  return src ? src.map(lm => lm ? { x: lm.x, y: lm.y, v: lm.v } : null) : null;
}

function computeMatchError(transformedPts, targetPts) {
  let s=0, c=0;
  for (let i = 0; i < transformedPts.length; i++) {
    const a = transformedPts[i], b = targetPts[i];
    if (!a || !b) continue;
    const dx = a.x - b.x, dy = a.y - b.y;
    s += dx*dx + dy*dy;
    c++;
  }
  return c ? s / c : Infinity;
}

function computeSimilarityTransform(srcPts, dstPts) {
  const valid = [];
  for (let i = 0; i < srcPts.length; i++) {
    const a = srcPts[i], b = dstPts[i];
    if (!a || !b) continue;
    valid.push({a,b});
  }
  if (valid.length < 2) return null;

  let sx=0, sy=0, dx=0, dy=0;
  for (const v of valid) { sx+=v.a.x; sy+=v.a.y; dx+=v.b.x; dy+=v.b.y; }
  const n = valid.length;
  const scx = sx / n, scy = sy / n, dcx = dx / n, dcy = dy / n;

  let Sxx=0, Sxy=0, denom=0;
  for (const v of valid) {
    const ax = v.a.x - scx, ay = v.a.y - scy;
    const bx = v.b.x - dcx, by = v.b.y - dcy;
    Sxx += ax * bx + ay * by;
    Sxy += ax * by - ay * bx;
    denom += ax*ax + ay*ay;
  }
  if (denom <= 1e-6) return null;

  const angle = Math.atan2(Sxy, Sxx);
  const scale = Sxx / denom;
  const tx = dcx - scale * ( Math.cos(angle) * scx - Math.sin(angle) * scy );
  const ty = dcy - scale * ( Math.sin(angle) * scx + Math.cos(angle) * scy );

  return { scale, angle, tx, ty };
}

function angDiff(a, b) {
  let d = a - b;
  while (d <= -Math.PI) d += 2*Math.PI;
  while (d > Math.PI) d -= 2*Math.PI;
  return d;
}

function applyTransformToPts(pts, T, doMirror=false, center=null) {
  if (!T) return pts.map(p => p ? { x: p.x, y: p.y, v: p.v } : null);
  const cosR = Math.cos(T.angle), sinR = Math.sin(T.angle);
  const out = [];
  for (const p of pts) {
    if (!p) { out.push(null); continue; }
    let x = p.x, y = p.y;
    if (doMirror) x = center ? (2*center.x - x) : -x;
    const nx = T.scale * (cosR * x - sinR * y) + T.tx;
    const ny = T.scale * (sinR * x + cosR * y) + T.ty;
    out.push({ x: nx, y: ny, v: p.v });
  }
  return out;
}

function enforceBoneConstraints(landmarks, connections, targetLengths, iterations = 2) {
  if (!landmarks || !connections || !targetLengths) return landmarks;
  
  const result = landmarks.map(p => p ? { x: p.x, y: p.y, v: p.v } : null);
  
  for (let iter = 0; iter < iterations; iter++) {
    for (let i = 0; i < connections.length; i++) {
      const [a, b] = connections[i];
      const pa = result[a], pb = result[b];
      const targetLen = targetLengths[i];
      
      if (!pa || !pb || !targetLen) continue;
      
      const dx = pb.x - pa.x;
      const dy = pb.y - pa.y;
      const currLen = Math.sqrt(dx * dx + dy * dy);
      
      if (currLen < 0.1) continue;
      
      const ratio = targetLen / currLen;
      const newBx = pa.x + dx * ratio;
      const newBy = pa.y + dy * ratio;
      
      pb.x = pa.x + (newBx - pa.x) * 0.5;
      pb.y = pa.y + (newBy - pa.y) * 0.5;
    }
  }
  
  return result;
}

function alignToPuppet(srcLandmarks) {
  if (!puppetTemplate) return srcLandmarks;

  const srcSel = ALIGN_INDICES.map(i => srcLandmarks[i] ? {x: srcLandmarks[i].x, y: srcLandmarks[i].y} : null);
  const dstSel = ALIGN_INDICES.map(i => puppetTemplate[i] ? {x: puppetTemplate[i].x, y: puppetTemplate[i].y} : null);

  const Tnm = computeSimilarityTransform(srcSel, dstSel);
  
  let centroid = null;
  {
    let sx=0, sy=0, cnt=0;
    for (const p of srcSel) if (p) { sx+=p.x; sy+=p.y; cnt++; }
    if (cnt) centroid = { x: sx/cnt, y: sy/cnt };
  }
  
  const srcSelMir = srcSel.map(p => p ? { x: (centroid ? 2*centroid.x - p.x : -p.x), y: p.y } : null);
  const Tm = computeSimilarityTransform(srcSelMir, dstSel);

  const srcAll = srcLandmarks.map(p => p ? {x:p.x,y:p.y} : null);
  let errNM = Infinity, errM = Infinity;
  if (Tnm) {
    const trgNM = applyTransformToPts(srcAll, Tnm, false);
    errNM = computeMatchError(trgNM, puppetTemplate);
  }
  if (Tm) {
    const trgM = applyTransformToPts(srcAll, Tm, false, null);
    errM = computeMatchError(trgM, puppetTemplate);
  }

  let decidedMirror = null;
  if (mirrorForced === true) decidedMirror = true;
  else if (mirrorForced === false) decidedMirror = false;
  else {
    let preferMirror = (errM < errNM * MIRROR_ERROR_RATIO);
    if (preferMirror) mirrorDecisionCounter = Math.min(mirrorDecisionCounter + 1, MIRROR_SWITCH_COUNT);
    else mirrorDecisionCounter = Math.max(mirrorDecisionCounter - 1, -MIRROR_SWITCH_COUNT);
    if (mirrorDecisionCounter >= MIRROR_SWITCH_COUNT) decidedMirror = true;
    else if (mirrorDecisionCounter <= -MIRROR_SWITCH_COUNT) decidedMirror = false;
    else decidedMirror = (mirrorDecisionCounter > 0);
  }

  const chosenT = decidedMirror ? Tm : Tnm;
  if (!chosenT) return srcLandmarks;

  if (!currentTransform) {
    currentTransform = chosenT;
  } else {
    currentTransform.scale = currentTransform.scale * (1 - TRANSFORM_LERP) + chosenT.scale * TRANSFORM_LERP;
    currentTransform.tx = currentTransform.tx * (1 - TRANSFORM_LERP) + chosenT.tx * TRANSFORM_LERP;
    currentTransform.ty = currentTransform.ty * (1 - TRANSFORM_LERP) + chosenT.ty * TRANSFORM_LERP;
    const delta = angDiff(chosenT.angle, currentTransform.angle);
    currentTransform.angle = currentTransform.angle + delta * TRANSFORM_LERP;
  }

  let out = applyTransformToPts(srcLandmarks, currentTransform, decidedMirror, centroid);
  
  // 应用骨骼约束
  if (boneLengths) {
    out = enforceBoneConstraints(out, POSE_CONNECTIONS, boneLengths, 3);
  }
  
  return out;
}

function findNearestIndex(x, y, list) {
  if (!list) return { idx: -1, d: Infinity };
  let best = -1, bd = Infinity;
  for (let i = 0; i < list.length; i++) {
    const p = list[i];
    if (!p) continue;
    const d = dist(x, y, p.x, p.y);
    if (d < bd) { bd = d; best = i; }
  }
  return { idx: best, d: bd };
}

// ============ setup ============
function setup() {
  const cnv = createCanvas(640, 480);
  cnv.id('p5canvas');

  videoEl = createVideo();
  videoEl.size(640, 480);
  videoEl.hide();

  const fileInput = document.getElementById('videoFile');
  fileInput.addEventListener('change', (e) => {
    const file = e.target.files[0];
    if (!file) return;
    trail = [];
    const url = URL.createObjectURL(file);
    videoEl.elt.src = url;
    videoEl.elt.load();
    videoEl.elt.onloadedmetadata = () => {
      videoEl.elt.muted = true;
      videoEl.elt.play().catch(err => console.warn('Autoplay blocked:', err));
    };
  });

  const sel = document.getElementById('landmarkSelect');
  LANDMARKS.forEach((name, i) => {
    const opt = document.createElement('option');
    opt.value = i;
    opt.text = `${i} - ${name}`;
    sel.appendChild(opt);
  });
  sel.value = selectedLandmark;
  sel.addEventListener('change', (e) => {
    selectedLandmark = parseInt(e.target.value);
    trail = [];
  });

  playBtn = document.getElementById('playBtn');
  playBtn.addEventListener('click', async () => {
    if (!videoEl || !videoEl.elt) return;
    try {
      if (videoEl.elt.paused) {
        videoEl.elt.muted = false;
        await videoEl.elt.play();
      } else {
        videoEl.elt.pause();
      }
    } catch (err) {
      console.error('Play error:', err);
    }
  });

  videoEl.elt.addEventListener('pause', () => { pausedFreeze = true; });
  videoEl.elt.addEventListener('play', () => { pausedFreeze = false; currentTransform = null; });

  pose = new Pose({
    locateFile: (file) => `https://cdn.jsdelivr.net/npm/@mediapipe/pose@0.5/${file}`
  });
  pose.setOptions({
    modelComplexity: 1,
    smoothLandmarks: true,
    enableSegmentation: false,
    minDetectionConfidence: 0.5,
    minTrackingConfidence: 0.5
  });
  pose.onResults(onPoseResults);
  
  pose.initialize().then(() => {
    poseReady = true;
    console.log('✓ MediaPipe Pose ready');
  }).catch((err) => console.error('Pose init failed:', err));

  createManualControls();
}

// ============ onPoseResults ============
function onPoseResults(results) {
  const vW = (videoEl && videoEl.elt && videoEl.elt.videoWidth) ? videoEl.elt.videoWidth : width;
  const vH = (videoEl && videoEl.elt && videoEl.elt.videoHeight) ? videoEl.elt.videoHeight : height;
  const scaleX = width / vW;
  const scaleY = height / vH;

  if (results.poseLandmarks && results.poseLandmarks.length) {
    if (!smoothedLandmarks || smoothedLandmarks.length !== results.poseLandmarks.length) {
      smoothedLandmarks = results.poseLandmarks.map(lm => ({
        x: (lm.x ?? 0) * vW * scaleX,
        y: (lm.y ?? 0) * vH * scaleY,
        v: lm.visibility ?? 1
      }));
      historyBuffers = smoothedLandmarks.map(() => ({ xs: [], ys: [], vs: [] }));
    } else {
      for (let i = 0; i < results.poseLandmarks.length; i++) {
        const lm = results.poseLandmarks[i];
        const currX = (lm.x ?? 0) * vW * scaleX;
        const currY = (lm.y ?? 0) * vH * scaleY;
        const currV = lm.visibility ?? 1;

        const buf = historyBuffers[i];
        buf.xs.push(currX); if (buf.xs.length > HIST_LEN) buf.xs.shift();
        buf.ys.push(currY); if (buf.ys.length > HIST_LEN) buf.ys.shift();
        buf.vs.push(currV); if (buf.vs.length > HIST_LEN) buf.vs.shift();

        function median(arr) {
          const a = arr.slice().sort((a,b)=>a-b);
          const m = Math.floor(a.length/2);
          return a.length % 2 ? a[m] : (a[m-1]+a[m]) / 2;
        }

        const medX = median(buf.xs);
        const medY = median(buf.ys);
        const medV = median(buf.vs);

        const prev = smoothedLandmarks[i];
        const alpha = (medV >= VISIBILITY_THRESHOLD) ? SMOOTH_ALPHA_HIGH : SMOOTH_ALPHA_LOW;
        const targetX = prev.x * EWMA_ALPHA + medX * (1 - EWMA_ALPHA);
        const targetY = prev.y * EWMA_ALPHA + medY * (1 - EWMA_ALPHA);
        const nextX = prev.x * alpha + targetX * (1 - alpha);
        const nextY = prev.y * alpha + targetY * (1 - alpha);
        const nextV = prev.v * alpha + medV * (1 - alpha);

        const d = dist(prev.x, prev.y, nextX, nextY);
        let finalX = nextX, finalY = nextY;
        if (d > MAX_JUMP_PX) {
          const t = MAX_JUMP_PX / d;
          finalX = prev.x + (nextX - prev.x) * t;
          finalY = prev.y + (nextY - prev.y) * t;
        }

        prev.x = finalX;
        prev.y = finalY;
        prev.v = nextV;
      }
    }

    if (!boneLengths) {
      let sumVis = 0, cntVis = 0;
      for (let i = 0; i < smoothedLandmarks.length; i++) {
        if (smoothedLandmarks[i]) { sumVis += smoothedLandmarks[i].v; cntVis++; }
      }
      const avgVis = cntVis ? sumVis / cntVis : 0;

      if (avgVis > 0.6) stableFrameCount++;
      else stableFrameCount = 0;

      if (stableFrameCount >= STABLE_FRAMES_THRESHOLD && !puppetTemplate) {
        puppetTemplate = copyLandmarks(smoothedLandmarks);
        boneLengths = POSE_CONNECTIONS.map(([a,b]) => {
          const A = puppetTemplate[a], B = puppetTemplate[b];
          return A && B ? dist(A.x, A.y, B.x, B.y) : null;
        });
        console.log(`✓ Template initialized (avgVis=${avgVis.toFixed(2)})`);
        stableFrameCount = 0;
      }
    }

    let finalLandmarks = smoothedLandmarks;
    if (enableAutoAlign && puppetTemplate) {
      finalLandmarks = alignToPuppet(smoothedLandmarks);
    }
    resultsForDraw = { poseLandmarks: finalLandmarks };
  }

  if (smoothedLandmarks && smoothedLandmarks[selectedLandmark]) {
    const lm = smoothedLandmarks[selectedLandmark];
    const vis = lm.v ?? 1;
    if (vis >= VISIBILITY_THRESHOLD) {
      const last = trail.length ? trail[trail.length - 1] : null;
      const distOk = !last || dist(lm.x, lm.y, last.x, last.y) >= TRAIL_MIN_DIST;
      if (distOk) {
        trail.push({ x: lm.x, y: lm.y, score: vis });
        if (trail.length > MAX_TRAIL) trail.shift();
      }
    }
  }
}

// ============ draw ============
function draw() {
  background(30);

  if (poseReady && videoEl && videoEl.elt && videoEl.elt.readyState >= 2 && !pausedFreeze) {
    try { pose.send({image: videoEl.elt}); } catch (err) { console.error('pose.send:', err); }
  }

  if (videoEl && videoEl.elt && videoEl.elt.videoWidth > 0) {
    push();
    image(videoEl, 0, 0, width, height);
    pop();
  }

  const displayLandmarks = (manualEditMode && puppetTemplate) ? puppetTemplate : (resultsForDraw?.poseLandmarks);

  if (displayLandmarks) {
    stroke(0, 200, 255, 220);
    strokeWeight(3);
    for (let i = 0; i < POSE_CONNECTIONS.length; i++) {
      const [aIdx, bIdx] = POSE_CONNECTIONS[i];
      const a = displayLandmarks[aIdx];
      const b = displayLandmarks[bIdx];
      if (!a || !b) continue;
      if ((a.v ?? 0) < VISIBILITY_THRESHOLD || (b.v ?? 0) < VISIBILITY_THRESHOLD) continue;
      line(a.x, a.y, b.x, b.y);
    }

    noStroke();
    fill(0, 255, 0);
    for (let i = 0; i < displayLandmarks.length; i++) {
      const lm = displayLandmarks[i];
      if ((lm.v ?? 0) < 0.15) continue;
      ellipse(lm.x, lm.y, 6, 6);
    }
  }

  noFill();
  strokeWeight(2);
  stroke(255, 0, 0, 200);
  beginShape();
  for (let i = 0; i < trail.length; i++) {
    vertex(trail[i].x, trail[i].y);
  }
  endShape();

  if (trail.length > 0) {
    fill(255, 200, 0);
    noStroke();
    ellipse(trail[trail.length - 1].x, trail[trail.length - 1].y, 10, 10);
  }

  // === 手动编辑模式显示 ===
  if (manualEditMode && puppetTemplate) {
    push();
    stroke(255, 140, 0, 200);
    strokeWeight(2);
    for (let i = 0; i < POSE_CONNECTIONS.length; i++) {
      const [a, b] = POSE_CONNECTIONS[i];
      const A = puppetTemplate[a], B = puppetTemplate[b];
      if (A && B) line(A.x, A.y, B.x, B.y);
    }
    
    noStroke();
    for (let i = 0; i < puppetTemplate.length; i++) {
      const p = puppetTemplate[i];
      if (!p) continue;
      fill(i === manualSelectedIdx ? [255, 50, 50] : [255, 160, 0]);
      ellipse(p.x, p.y, i === manualSelectedIdx ? 12 : 8, i === manualSelectedIdx ? 12 : 8);
    }
    
    if (manualHoverIndex >= 0 && puppetTemplate[manualHoverIndex]) {
      noFill();
      stroke(255, 50, 50);
      strokeWeight(2);
      ellipse(puppetTemplate[manualHoverIndex].x, puppetTemplate[manualHoverIndex].y, 24, 24);
    }
    
    noStroke();
    fill(255);
    textSize(12);
    textAlign(LEFT, TOP);
    text('Manual Edit: drag to move | ENTER to apply', 8, 8);
    pop();
  }

  // === Click-to-Set 模式显示 ===
  if (setupMode && puppetTemplate) {
    push();
    // 显示已设置的点（高亮关键点）
    noStroke();
    fill(0, 255, 100, 150);
    for (let i = 0; i < setupPointIdx; i++) {
      const idx = CRITICAL_POINTS[i];
      const p = puppetTemplate[idx];
      if (p && (p.x || p.y)) {
        ellipse(p.x, p.y, 10, 10);
      }
    }
    
    // 显示十字光标
    stroke(255, 200, 0, 200);
    strokeWeight(1);
    line(mouseX - 15, mouseY, mouseX + 15, mouseY);
    line(mouseX, mouseY - 15, mouseX, mouseY + 15);
    
    noStroke();
    fill(255, 200, 0);
    textSize(14);
    textAlign(CENTER, BOTTOM);
    const currentPointName = CRITICAL_NAMES[setupPointIdx];
    text(`${setupPointIdx + 1}/13: Click to set ${currentPointName}`, width / 2, 20);
    
    // 左下角显示已完成的点列表
    fill(200, 200, 200);
    textSize(10);
    textAlign(LEFT, TOP);
    let yPos = height - 100;
    text('✓ Completed:', 10, yPos);
    for (let i = 0; i < setupPointIdx; i++) {
      yPos += 12;
      text(`${i + 1}. ${CRITICAL_NAMES[i]}`, 15, yPos);
    }
    
    pop();
  }
}

// 修改 mousePressed 以支持 Click-to-Set
function mousePressed() {
  if (setupMode) {
    if (mouseX < 0 || mouseY < 0 || mouseX > width || mouseY > height) return;
    const pointIdx = CRITICAL_POINTS[setupPointIdx];
    puppetTemplate[pointIdx] = { x: mouseX, y: mouseY, v: 1 };
    console.log(`Set ${LANDMARKS[pointIdx]} (#${pointIdx}): (${Math.round(mouseX)}, ${Math.round(mouseY)})`);
    setupPointIdx++;
    return;
  }

  if (!manualEditMode || !puppetTemplate) return;
  if (mouseX < 0 || mouseY < 0 || mouseX > width || mouseY > height) return;
  const { idx, d } = findNearestIndex(mouseX, mouseY, puppetTemplate);
  if (idx >= 0 && d < 30) { manualSelectedIdx = idx; manualDragging = true; }
}

// ============ 手动控制 UI ============
function createManualControls() {
  const container = document.createElement('div');
  container.style.position = 'fixed';
  container.style.left = '10px';
  container.style.bottom = '10px';
  container.style.background = 'rgba(0,0,0,0.85)';
  container.style.color = '#fff';
  container.style.padding = '10px';
  container.style.zIndex = 9999;
  container.style.fontSize = '11px';
  container.style.maxWidth = '350px';
  container.style.borderRadius = '4px';

  // === 第一行：模板初始化选项 ===
  const row1 = document.createElement('div');
  row1.style.marginBottom = '8px';

  const label1 = document.createElement('span');
  label1.textContent = '📋 Template Setup:';
  label1.style.fontWeight = 'bold';
  label1.style.display = 'block';
  label1.style.marginBottom = '4px';
  row1.appendChild(label1);

  const freezeBtn = document.createElement('button');
  freezeBtn.textContent = '1. Auto Freeze (from detect)';
  freezeBtn.style.marginRight = '6px';
  freezeBtn.style.marginBottom = '4px';
  freezeBtn.style.padding = '4px 6px';
  freezeBtn.style.background = '#445';
  freezeBtn.onclick = () => {
    if (!resultsForDraw?.poseLandmarks && !smoothedLandmarks) {
      alert('❌ No pose detected. Make sure video is playing.');
      return;
    }
    const src = resultsForDraw?.poseLandmarks || smoothedLandmarks;
    puppetTemplate = copyLandmarks(src);
    boneLengths = POSE_CONNECTIONS.map(([a,b]) => {
      const A = puppetTemplate[a], B = puppetTemplate[b];
      return A && B ? dist(A.x, A.y, B.x, B.y) : null;
    });
    console.log('✓ Auto template frozen from detection');
    alert('✓ Template frozen from current detection.\n\nNow use Manual Edit to adjust points to match puppet image.');
  };
  row1.appendChild(freezeBtn);

  const manualSetBtn = document.createElement('button');
  manualSetBtn.textContent = `2. Click-to-Set (${CRITICAL_POINTS.length} points)`;
  manualSetBtn.style.padding = '4px 6px';
  manualSetBtn.style.background = '#544';
  manualSetBtn.onclick = () => {
    if (!puppetTemplate) {
      puppetTemplate = Array(33).fill(null).map(() => ({ x: 0, y: 0, v: 1 }));
    }
    setupMode = !setupMode;
    if (setupMode) setupPointIdx = 0; // 重置索引
    manualSetBtn.style.background = setupMode ? '#655' : '#544';
    manualSetBtn.textContent = setupMode ? `✓ Setting Mode ON (${setupPointIdx}/${CRITICAL_POINTS.length})` : `2. Click-to-Set (${CRITICAL_POINTS.length} points)`;
    if (setupMode) {
      console.log(`🖱️ Click-to-Set mode: Only need to set ${CRITICAL_POINTS.length} critical points`);
      alert(`Click-to-Set Mode Active!\n\nOnly need to click ${CRITICAL_POINTS.length} critical points:\n${CRITICAL_NAMES.join(', ')}\n\nPress ENTER when done, ESC to cancel.`);
    }
  };
  row1.appendChild(manualSetBtn);
  container.appendChild(row1);

  // === 第二行：对齐控制 ===
  const row2 = document.createElement('div');
  row2.style.marginBottom = '8px';

  const label2 = document.createElement('span');
  label2.textContent = '⚙️ Alignment:';
  label2.style.fontWeight = 'bold';
  label2.style.display = 'block';
  label2.style.marginBottom = '4px';
  row2.appendChild(label2);

  const alignToggle = document.createElement('button');
  alignToggle.textContent = `AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
  alignToggle.style.marginRight = '6px';
  alignToggle.style.padding = '4px 6px';
  alignToggle.style.background = enableAutoAlign ? '#4a4' : '#a44';
  alignToggle.onclick = () => {
    enableAutoAlign = !enableAutoAlign;
    alignToggle.textContent = `AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
    alignToggle.style.background = enableAutoAlign ? '#4a4' : '#a44';
    console.log(`AutoAlign ${enableAutoAlign ? 'enabled' : 'disabled'}`);
  };
  row2.appendChild(alignToggle);

  const manualToggle = document.createElement('button');
  manualToggle.textContent = 'Manual Edit';
  manualToggle.style.padding = '4px 6px';
  manualToggle.style.background = '#545';
  manualToggle.onclick = () => {
    if (!puppetTemplate) {
      alert('❌ Must set template first! Use "Auto Freeze" or "Click-to-Set"');
      return;
    }
    manualEditMode = !manualEditMode;
    manualToggle.textContent = manualEditMode ? '✓ Editing' : 'Manual Edit';
    manualToggle.style.background = manualEditMode ? '#655' : '#545';
  };
  row2.appendChild(manualToggle);
  container.appendChild(row2);

  // === 第三行：导入/导出 ===
  const row3 = document.createElement('div');
  row3.style.marginBottom = '8px';

  const label3 = document.createElement('span');
  label3.textContent = '💾 Save/Load:';
  label3.style.fontWeight = 'bold';
  label3.style.display = 'block';
  label3.style.marginBottom = '4px';
  row3.appendChild(label3);

  const expBtn = document.createElement('button');
  expBtn.textContent = 'Export';
  expBtn.style.marginRight = '6px';
  expBtn.style.padding = '4px 6px';
  expBtn.style.background = '#445';
  expBtn.onclick = () => {
    if (!puppetTemplate) {
      alert('No template to export');
      return;
    }
    const data = { puppetTemplate, boneLengths };
    const a = document.createElement('a');
    a.href = 'data:application/json;charset=utf-8,' + encodeURIComponent(JSON.stringify(data, null, 2));
    a.download = `puppet_${Date.now()}.json`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    console.log('✓ Template exported');
  };
  row3.appendChild(expBtn);

  const impInput = document.createElement('input');
  impInput.type = 'file';
  impInput.accept = '.json';
  impInput.style.fontSize = '10px';
  impInput.style.padding = '2px';
  impInput.onchange = (ev) => {
    const f = ev.target.files[0];
    if (!f) return;
    const r = new FileReader();
    r.onload = (e) => {
      try {
        const obj = JSON.parse(e.target.result);
        if (obj.puppetTemplate && Array.isArray(obj.puppetTemplate)) {
          puppetTemplate = obj.puppetTemplate;
          boneLengths = obj.boneLengths || null;
          console.log('✓ Template imported');
          alert('✓ Template imported successfully!');
        } else {
          alert('Invalid template format');
        }
      } catch (err) {
        alert('Parse error: ' + err.message);
      }
    };
    r.readAsText(f);
  };
  row3.appendChild(impInput);
  container.appendChild(row3);

  // === 第四行：重置 ===
  const row4 = document.createElement('div');
  const resetBtn = document.createElement('button');
  resetBtn.textContent = 'Reset All';
  resetBtn.style.padding = '4px 6px';
  resetBtn.style.background = '#a44';
  resetBtn.onclick = () => {
    if (confirm('Reset all templates and settings?')) {
      puppetTemplate = null;
      boneLengths = null;
      currentTransform = null;
      setupMode = false;
      setupPointIdx = 0;
      manualEditMode = false;
      enableAutoAlign = true;
      stableFrameCount = 0;
      console.log('✓ Reset complete');
    }
  };
  row4.appendChild(resetBtn);
  container.appendChild(row4);

  // === 状态显示 ===
  const statusDiv = document.createElement('div');
  statusDiv.id = 'controlStatus';
  statusDiv.style.fontSize = '10px';
  statusDiv.style.color = '#aaa';
  statusDiv.style.marginTop = '8px';
  statusDiv.style.borderTop = '1px solid #555';
  statusDiv.style.paddingTop = '4px';
  statusDiv.textContent = '📊 Status: Ready';
  container.appendChild(statusDiv);

  document.body.appendChild(container);

  setInterval(() => {
    if (setupMode) {
      statusDiv.textContent = `🖱️ Setup Mode: ${setupPointIdx}/${CRITICAL_POINTS.length} points set`;
      statusDiv.style.color = '#ff9';
      // 更新按钮显示进度
      manualSetBtn.textContent = `✓ Setting Mode ON (${setupPointIdx}/${CRITICAL_POINTS.length})`;
    } else if (manualEditMode) {
      statusDiv.textContent = '✏️ Manual Edit Mode: Drag points to adjust';
      statusDiv.style.color = '#9ff';
    } else if (puppetTemplate) {
      statusDiv.textContent = `✓ Template ready | AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
      statusDiv.style.color = '#9f9';
    } else {
      statusDiv.textContent = 'Status: Waiting for template setup';
      statusDiv.style.color = '#f99';
    }
  }, 500);
}

// ============ 新增：简化的关键点集合 ============
// 只需点击这 12 个关键点，其他点会自动从检测结果推导
const CRITICAL_POINTS = [
  0,   // nose
  11,  // left_shoulder
  12,  // right_shoulder
  13,  // left_elbow
  14,  // right_elbow
  15,  // left_wrist
  16,  // right_wrist
  23,  // left_hip
  24,  // right_hip
  25,  // left_knee
  26,  // right_knee
  27,  // left_ankle
  28   // right_ankle
];

const CRITICAL_NAMES = [
  "nose",
  "left_shoulder", "right_shoulder",
  "left_elbow", "right_elbow",
  "left_wrist", "right_wrist",
  "left_hip", "right_hip",
  "left_knee", "right_knee",
  "left_ankle", "right_ankle"
];

// 修改 draw() 中添加 Click-to-Set 的可视反馈
function draw() {
  background(30);

  if (poseReady && videoEl && videoEl.elt && videoEl.elt.readyState >= 2 && !pausedFreeze) {
    try { pose.send({image: videoEl.elt}); } catch (err) { console.error('pose.send:', err); }
  }

  if (videoEl && videoEl.elt && videoEl.elt.videoWidth > 0) {
    push();
    image(videoEl, 0, 0, width, height);
    pop();
  }

  const displayLandmarks = (manualEditMode && puppetTemplate) ? puppetTemplate : (resultsForDraw?.poseLandmarks);

  if (displayLandmarks) {
    stroke(0, 200, 255, 220);
    strokeWeight(3);
    for (let i = 0; i < POSE_CONNECTIONS.length; i++) {
      const [aIdx, bIdx] = POSE_CONNECTIONS[i];
      const a = displayLandmarks[aIdx];
      const b = displayLandmarks[bIdx];
      if (!a || !b) continue;
      if ((a.v ?? 0) < VISIBILITY_THRESHOLD || (b.v ?? 0) < VISIBILITY_THRESHOLD) continue;
      line(a.x, a.y, b.x, b.y);
    }

    noStroke();
    fill(0, 255, 0);
    for (let i = 0; i < displayLandmarks.length; i++) {
      const lm = displayLandmarks[i];
      if ((lm.v ?? 0) < 0.15) continue;
      ellipse(lm.x, lm.y, 6, 6);
    }
  }

  noFill();
  strokeWeight(2);
  stroke(255, 0, 0, 200);
  beginShape();
  for (let i = 0; i < trail.length; i++) {
    vertex(trail[i].x, trail[i].y);
  }
  endShape();

  if (trail.length > 0) {
    fill(255, 200, 0);
    noStroke();
    ellipse(trail[trail.length - 1].x, trail[trail.length - 1].y, 10, 10);
  }

  // === 手动编辑模式显示 ===
  if (manualEditMode && puppetTemplate) {
    push();
    stroke(255, 140, 0, 200);
    strokeWeight(2);
    for (let i = 0; i < POSE_CONNECTIONS.length; i++) {
      const [a, b] = POSE_CONNECTIONS[i];
      const A = puppetTemplate[a], B = puppetTemplate[b];
      if (A && B) line(A.x, A.y, B.x, B.y);
    }
    
    noStroke();
    for (let i = 0; i < puppetTemplate.length; i++) {
      const p = puppetTemplate[i];
      if (!p) continue;
      fill(i === manualSelectedIdx ? [255, 50, 50] : [255, 160, 0]);
      ellipse(p.x, p.y, i === manualSelectedIdx ? 12 : 8, i === manualSelectedIdx ? 12 : 8);
    }
    
    if (manualHoverIndex >= 0 && puppetTemplate[manualHoverIndex]) {
      noFill();
      stroke(255, 50, 50);
      strokeWeight(2);
      ellipse(puppetTemplate[manualHoverIndex].x, puppetTemplate[manualHoverIndex].y, 24, 24);
    }
    
    noStroke();
    fill(255);
    textSize(12);
    textAlign(LEFT, TOP);
    text('Manual Edit: drag to move | ENTER to apply', 8, 8);
    pop();
  }

  // === Click-to-Set 模式显示 ===
  if (setupMode && puppetTemplate) {
    push();
    // 显示已设置的点（高亮关键点）
    noStroke();
    fill(0, 255, 100, 150);
    for (let i = 0; i < setupPointIdx; i++) {
      const idx = CRITICAL_POINTS[i];
      const p = puppetTemplate[idx];
      if (p && (p.x || p.y)) {
        ellipse(p.x, p.y, 10, 10);
      }
    }
    
    // 显示十字光标
    stroke(255, 200, 0, 200);
    strokeWeight(1);
    line(mouseX - 15, mouseY, mouseX + 15, mouseY);
    line(mouseX, mouseY - 15, mouseX, mouseY + 15);
    
    noStroke();
    fill(255, 200, 0);
    textSize(14);
    textAlign(CENTER, BOTTOM);
    const currentPointName = CRITICAL_NAMES[setupPointIdx];
    text(`${setupPointIdx + 1}/13: Click to set ${currentPointName}`, width / 2, 20);
    
    // 左下角显示已完成的点列表
    fill(200, 200, 200);
    textSize(10);
    textAlign(LEFT, TOP);
    let yPos = height - 100;
    text('✓ Completed:', 10, yPos);
    for (let i = 0; i < setupPointIdx; i++) {
      yPos += 12;
      text(`${i + 1}. ${CRITICAL_NAMES[i]}`, 15, yPos);
    }
    
    pop();
  }
}

// 修改 createManualControls 中的 Click-to-Set 按钮逻辑
function createManualControls() {
  const container = document.createElement('div');
  container.style.position = 'fixed';
  container.style.left = '10px';
  container.style.bottom = '10px';
  container.style.background = 'rgba(0,0,0,0.85)';
  container.style.color = '#fff';
  container.style.padding = '10px';
  container.style.zIndex = 9999;
  container.style.fontSize = '11px';
  container.style.maxWidth = '350px';
  container.style.borderRadius = '4px';

  // === 第一行：模板初始化选项 ===
  const row1 = document.createElement('div');
  row1.style.marginBottom = '8px';

  const label1 = document.createElement('span');
  label1.textContent = '📋 Template Setup:';
  label1.style.fontWeight = 'bold';
  label1.style.display = 'block';
  label1.style.marginBottom = '4px';
  row1.appendChild(label1);

  const freezeBtn = document.createElement('button');
  freezeBtn.textContent = '1. Auto Freeze (from detect)';
  freezeBtn.style.marginRight = '6px';
  freezeBtn.style.marginBottom = '4px';
  freezeBtn.style.padding = '4px 6px';
  freezeBtn.style.background = '#445';
  freezeBtn.onclick = () => {
    if (!resultsForDraw?.poseLandmarks && !smoothedLandmarks) {
      alert('❌ No pose detected. Make sure video is playing.');
      return;
    }
    const src = resultsForDraw?.poseLandmarks || smoothedLandmarks;
    puppetTemplate = copyLandmarks(src);
    boneLengths = POSE_CONNECTIONS.map(([a,b]) => {
      const A = puppetTemplate[a], B = puppetTemplate[b];
      return A && B ? dist(A.x, A.y, B.x, B.y) : null;
    });
    console.log('✓ Auto template frozen from detection');
    alert('✓ Template frozen from current detection.\n\nNow use Manual Edit to adjust points to match puppet image.');
  };
  row1.appendChild(freezeBtn);

  const manualSetBtn = document.createElement('button');
  manualSetBtn.textContent = `2. Click-to-Set (${CRITICAL_POINTS.length} points)`;
  manualSetBtn.style.padding = '4px 6px';
  manualSetBtn.style.background = '#544';
  manualSetBtn.onclick = () => {
    if (!puppetTemplate) {
      puppetTemplate = Array(33).fill(null).map(() => ({ x: 0, y: 0, v: 1 }));
    }
    setupMode = !setupMode;
    if (setupMode) setupPointIdx = 0; // 重置索引
    manualSetBtn.style.background = setupMode ? '#655' : '#544';
    manualSetBtn.textContent = setupMode ? `✓ Setting Mode ON (${setupPointIdx}/${CRITICAL_POINTS.length})` : `2. Click-to-Set (${CRITICAL_POINTS.length} points)`;
    if (setupMode) {
      console.log(`🖱️ Click-to-Set mode: Only need to set ${CRITICAL_POINTS.length} critical points`);
      alert(`Click-to-Set Mode Active!\n\nOnly need to click ${CRITICAL_POINTS.length} critical points:\n${CRITICAL_NAMES.join(', ')}\n\nPress ENTER when done, ESC to cancel.`);
    }
  };
  row1.appendChild(manualSetBtn);
  container.appendChild(row1);

  // === 第二行：对齐控制 ===
  const row2 = document.createElement('div');
  row2.style.marginBottom = '8px';

  const label2 = document.createElement('span');
  label2.textContent = '⚙️ Alignment:';
  label2.style.fontWeight = 'bold';
  label2.style.display = 'block';
  label2.style.marginBottom = '4px';
  row2.appendChild(label2);

  const alignToggle = document.createElement('button');
  alignToggle.textContent = `AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
  alignToggle.style.marginRight = '6px';
  alignToggle.style.padding = '4px 6px';
  alignToggle.style.background = enableAutoAlign ? '#4a4' : '#a44';
  alignToggle.onclick = () => {
    enableAutoAlign = !enableAutoAlign;
    alignToggle.textContent = `AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
    alignToggle.style.background = enableAutoAlign ? '#4a4' : '#a44';
    console.log(`AutoAlign ${enableAutoAlign ? 'enabled' : 'disabled'}`);
  };
  row2.appendChild(alignToggle);

  const manualToggle = document.createElement('button');
  manualToggle.textContent = 'Manual Edit';
  manualToggle.style.padding = '4px 6px';
  manualToggle.style.background = '#545';
  manualToggle.onclick = () => {
    if (!puppetTemplate) {
      alert('❌ Must set template first! Use "Auto Freeze" or "Click-to-Set"');
      return;
    }
    manualEditMode = !manualEditMode;
    manualToggle.textContent = manualEditMode ? '✓ Editing' : 'Manual Edit';
    manualToggle.style.background = manualEditMode ? '#655' : '#545';
  };
  row2.appendChild(manualToggle);
  container.appendChild(row2);

  // === 第三行：导入/导出 ===
  const row3 = document.createElement('div');
  row3.style.marginBottom = '8px';

  const label3 = document.createElement('span');
  label3.textContent = '💾 Save/Load:';
  label3.style.fontWeight = 'bold';
  label3.style.display = 'block';
  label3.style.marginBottom = '4px';
  row3.appendChild(label3);

  const expBtn = document.createElement('button');
  expBtn.textContent = 'Export';
  expBtn.style.marginRight = '6px';
  expBtn.style.padding = '4px 6px';
  expBtn.style.background = '#445';
  expBtn.onclick = () => {
    if (!puppetTemplate) {
      alert('No template to export');
      return;
    }
    const data = { puppetTemplate, boneLengths };
    const a = document.createElement('a');
    a.href = 'data:application/json;charset=utf-8,' + encodeURIComponent(JSON.stringify(data, null, 2));
    a.download = `puppet_${Date.now()}.json`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    console.log('✓ Template exported');
  };
  row3.appendChild(expBtn);

  const impInput = document.createElement('input');
  impInput.type = 'file';
  impInput.accept = '.json';
  impInput.style.fontSize = '10px';
  impInput.style.padding = '2px';
  impInput.onchange = (ev) => {
    const f = ev.target.files[0];
    if (!f) return;
    const r = new FileReader();
    r.onload = (e) => {
      try {
        const obj = JSON.parse(e.target.result);
        if (obj.puppetTemplate && Array.isArray(obj.puppetTemplate)) {
          puppetTemplate = obj.puppetTemplate;
          boneLengths = obj.boneLengths || null;
          console.log('✓ Template imported');
          alert('✓ Template imported successfully!');
        } else {
          alert('Invalid template format');
        }
      } catch (err) {
        alert('Parse error: ' + err.message);
      }
    };
    r.readAsText(f);
  };
  row3.appendChild(impInput);
  container.appendChild(row3);

  // === 第四行：重置 ===
  const row4 = document.createElement('div');
  const resetBtn = document.createElement('button');
  resetBtn.textContent = 'Reset All';
  resetBtn.style.padding = '4px 6px';
  resetBtn.style.background = '#a44';
  resetBtn.onclick = () => {
    if (confirm('Reset all templates and settings?')) {
      puppetTemplate = null;
      boneLengths = null;
      currentTransform = null;
      setupMode = false;
      setupPointIdx = 0;
      manualEditMode = false;
      enableAutoAlign = true;
      stableFrameCount = 0;
      console.log('✓ Reset complete');
    }
  };
  row4.appendChild(resetBtn);
  container.appendChild(row4);

  // === 状态显示 ===
  const statusDiv = document.createElement('div');
  statusDiv.id = 'controlStatus';
  statusDiv.style.fontSize = '10px';
  statusDiv.style.color = '#aaa';
  statusDiv.style.marginTop = '8px';
  statusDiv.style.borderTop = '1px solid #555';
  statusDiv.style.paddingTop = '4px';
  statusDiv.textContent = '📊 Status: Ready';
  container.appendChild(statusDiv);

  document.body.appendChild(container);

  setInterval(() => {
    if (setupMode) {
      statusDiv.textContent = `🖱️ Setup Mode: ${setupPointIdx}/${CRITICAL_POINTS.length} points set`;
      statusDiv.style.color = '#ff9';
      // 更新按钮显示进度
      manualSetBtn.textContent = `✓ Setting Mode ON (${setupPointIdx}/${CRITICAL_POINTS.length})`;
    } else if (manualEditMode) {
      statusDiv.textContent = '✏️ Manual Edit Mode: Drag points to adjust';
      statusDiv.style.color = '#9ff';
    } else if (puppetTemplate) {
      statusDiv.textContent = `✓ Template ready | AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
      statusDiv.style.color = '#9f9';
    } else {
      statusDiv.textContent = 'Status: Waiting for template setup';
      statusDiv.style.color = '#f99';
    }
  }, 500);
}

// 新增：Click-to-Set 模式全局变量
let setupMode = false;
let setupPointIdx = 0;

// 修改快捷键支持
window.addEventListener('keydown', (e) => {
  if (e.key === 'Enter') {
    if (setupMode) {
      setupMode = false;
      boneLengths = POSE_CONNECTIONS.map(([a,b]) => {
        const A = puppetTemplate[a], B = puppetTemplate[b];
        return A && B ? dist(A.x, A.y, B.x, B.y) : null;
      });
      console.log('✓ Click-to-Set setup complete');
      alert('✓ Template setup complete! Now use Manual Edit to fine-tune.');
      setupPointIdx = 0;
    }
  } else if (e.key === 'Escape') {
    if (setupMode) {
      setupMode = false;
      setupPointIdx = 0;
      console.log('✗ Click-to-Set cancelled');
    } else if (manualEditMode) {
      manualEditMode = false;
      console.log('✓ Manual edit exited');
    }
  } else if (e.key === 'd' || e.key === 'D') {
    if (resultsForDraw?.poseLandmarks && puppetTemplate) {
      const err = computeMatchError(resultsForDraw.poseLandmarks, puppetTemplate);
      console.log(`📊 Alignment Error: ${err.toFixed(2)}`);
    }
  } else if (e.key === 'Tab' && setupMode) {
    // TAB 键跳过当前点
    setupPointIdx = Math.min(setupPointIdx + 1, CRITICAL_POINTS.length);
    console.log(`⏭️ Skipped to point ${setupPointIdx}`);
  }
});
