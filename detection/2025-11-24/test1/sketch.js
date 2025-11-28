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

// ✨ 新增：动态 canvas 尺寸
let canvasWidth = 640;
let canvasHeight = 480;

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

// 简化的关键点集合
const CRITICAL_POINTS = [0, 11, 12, 13, 14, 15, 16, 23, 24, 25, 26, 27, 28];
const CRITICAL_NAMES = ["nose", "left_shoulder", "right_shoulder", "left_elbow", "right_elbow", 
                        "left_wrist", "right_wrist", "left_hip", "right_hip", "left_knee", "right_knee", "left_ankle", "right_ankle"];

// 平滑相关
let smoothedLandmarks = null;
const SMOOTH_ALPHA_HIGH = 0.3;   // 从 0.75 → 0.3（更快响应）
const SMOOTH_ALPHA_LOW = 0.5;    // 从 0.90 → 0.5（更快响应）
const VISIBILITY_THRESHOLD = 0.35;
const TRAIL_MIN_DIST = 3;
const MAX_JUMP_PX = 60;
const HIST_LEN = 3;  // 降低：从 5 → 3
const EWMA_ALPHA = 0.80;
let historyBuffers = null;

// 对齐相关
let puppetTemplate = null;
let boneLengths = null;
let mirrorForced = null;
let currentTransform = null;
const TRANSFORM_LERP = 0.05;

// ✨ 改进：仅用躯干关键点（最稳定）
const ALIGN_INDICES = [
  11, 12,  // 左右肩膀
  23, 24,  // 左右髋部
  25, 26,  // 左右膝盖（新增）
  27, 28   // 左右踝部（新增）
];

// ⚡ 改进：镜像决策稳定化（玻璃态转换）
let cachedMirrorDecision = false;
let mirrorDecisionMade = false;
let mirrorConsecutiveFrames = 0;
let lastMirrorVote = null;
const MIRROR_FRAMES_THRESHOLD = 30;  // 增加：从 20 → 30（更稳定）
const MIRROR_HYSTERESIS = 1.15;  // ✨ 新增：玻璃态因子（防止频繁切换）

let lastAlignErr = Infinity;
let alignmentSkipCounter = 0;
const ALIGNMENT_UPDATE_INTERVAL = 1;  // 从 4 → 1（每帧更新镜像决策）

// 手动编辑相关
let manualEditMode = false;
let manualSelectedIdx = -1;
let manualHoverIndex = -1;
let manualDragging = false;
let enableAutoAlign = true;
let stableFrameCount = 0;
const STABLE_FRAMES_THRESHOLD = 15;

// Click-to-Set 模式
let setupMode = false;
let setupPointIdx = 0;

// ⚡ 性能优化：帧跳过
let frameCounter = 0;
const POSE_SKIP_FRAMES = 0;  // 从 1 → 0（每帧推理）

// 脚部相关
const FOOT_INDICES = [27, 28, 29, 30, 31, 32];  // 踝部、脚跟、脚趾
const FOOT_PARENT = [25, 26];  // 膝盖（脚部的父节点）
let footPredictionBuffer = {};  // 脚部预测缓冲

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

  // ✨ 改进：计算中心点
  let sx=0, sy=0, dx=0, dy=0;
  for (const v of valid) { sx+=v.a.x; sy+=v.a.y; dx+=v.b.x; dy+=v.b.y; }
  const n = valid.length;
  const scx = sx / n, scy = sy / n, dcx = dx / n, dcy = dy / n;

  // ✨ 改进：使用更稳定的旋转+缩放计算
  let sumSrcSq = 0, sumDotProd = 0;
  let Hxx = 0, Hxy = 0, Hyx = 0, Hyy = 0;

  for (const v of valid) {
    const ax = v.a.x - scx, ay = v.a.y - scy;
    const bx = v.b.x - dcx, by = v.b.y - dcy;
    
    sumSrcSq += ax * ax + ay * ay;
    sumDotProd += ax * bx + ay * by;
    
    Hxx += ax * bx;
    Hxy += ax * by;
    Hyx += ay * bx;
    Hyy += ay * by;
  }

  // ✨ SVD：计算最优旋转
  const trace = Hxx + Hyy;
  const det = Hxx * Hyy - Hxy * Hyx;
  
  let angle = Math.atan2(Hyx - Hxy, Hxx + Hyy);
  let scale = 1;
  
  if (sumSrcSq > 0) {
    // 使用 Procrustes 分析计算缩放
    const numerator = Math.sqrt(det * det + trace * trace);
    scale = numerator / sumSrcSq;
  }

  // ✨ 防止异常缩放（0.5-2.0 范围）
  scale = Math.max(0.5, Math.min(2.0, scale));

  const cosR = Math.cos(angle);
  const sinR = Math.sin(angle);
  const tx = dcx - (cosR * scx - sinR * scy) * scale;
  const ty = dcy - (sinR * scx + cosR * scy) * scale;

  return { scale, angle, tx, ty };
}

function angDiff(a, b) {
  let d = a - b;
  while (d <= -Math.PI) d += 2*Math.PI;
  while (d > Math.PI) d -= 2*Math.PI;
  return d;
}

function applyTransformToPts(pts, transform, isMirrored, centroid) {
  if (!transform) return pts;

  const { scale, angle, tx, ty } = transform;
  const cosR = Math.cos(angle);
  const sinR = Math.sin(angle);

  return pts.map(p => {
    if (!p) return null;
    
    let x = p.x, y = p.y;

    // ✨ 镜像处理（如果需要）
    if (isMirrored && centroid) {
      x = 2 * centroid.x - x;
    }

    // ✨ 应用旋转和缩放
    const px = (x - centroid?.x ?? 0) * scale;
    const py = (y - centroid?.y ?? 0) * scale;
    const nx = cosR * px - sinR * py;
    const ny = sinR * px + cosR * py;

    return {
      x: nx + tx,
      y: ny + ty,
      v: p.v
    };
  });
}

// ⚡ 优化：只在必要时调用约束（不是每帧都调）
function enforceBoneConstraints(landmarks, connections, targetLengths, iterations = 1) {
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

  // ✨ 简化：不使用脚部进行对齐（脚部不稳定）
  // 只使用躯干+腿部关键点
  const srcSel = [
    srcLandmarks[11],  // 左肩
    srcLandmarks[12],  // 右肩
    srcLandmarks[23],  // 左髋
    srcLandmarks[24],  // 右髋
    srcLandmarks[25],  // 左膝
    srcLandmarks[26]   // 右膝
  ].map(lm => (lm && (lm.v ?? 0) >= 0.3) ? {x: lm.x, y: lm.y} : null);

  const dstSel = [
    puppetTemplate[11],
    puppetTemplate[12],
    puppetTemplate[23],
    puppetTemplate[24],
    puppetTemplate[25],
    puppetTemplate[26]
  ].map(lm => lm ? {x: lm.x, y: lm.y} : null);

  const validCount = srcSel.filter(p => p !== null).length;
  if (validCount < 3) {
    // 回退到只用躯干
    const srcSelTorso = [11, 12, 23, 24].map(i => srcLandmarks[i] ? {x: srcLandmarks[i].x, y: srcLandmarks[i].y} : null);
    const dstSelTorso = [11, 12, 23, 24].map(i => puppetTemplate[i] ? {x: puppetTemplate[i].x, y: puppetTemplate[i].y} : null);
    return alignToPuppetWithPoints(srcLandmarks, srcSelTorso, dstSelTorso);
  }

  return alignToPuppetWithPoints(srcLandmarks, srcSel, dstSel);
}

// ✨ 改进对齐逻辑
function alignToPuppetWithPoints(srcLandmarks, srcSel, dstSel) {
  const Tnm = computeSimilarityTransform(srcSel, dstSel);
  
  let centroid = null;
  {
    let sx=0, sy=0, cnt=0;
    for (const p of srcSel) if (p) { sx+=p.x; sy+=p.y; cnt++; }
    if (cnt) centroid = { x: sx/cnt, y: sy/cnt };
  }
  
  const srcSelMir = srcSel.map(p => p ? { x: (centroid ? 2*centroid.x - p.x : p.x), y: p.y } : null);
  const Tm = computeSimilarityTransform(srcSelMir, dstSel);

  const srcAll = srcLandmarks.map(p => p ? {x:p.x,y:p.y,v:p.v} : null);
  let errNM = Infinity, errM = Infinity;
  
  if (Tnm) {
    const trgNM = applyTransformToPts(srcAll, Tnm, false, centroid);
    errNM = 0;
    let cnt = 0;
    for (let i = 0; i < trgNM.length; i++) {
      const a = trgNM[i], b = puppetTemplate[i];
      if (!a || !b) continue;
      if ((a.v ?? 0) >= VISIBILITY_THRESHOLD) {
        const dx = a.x - b.x, dy = a.y - b.y;
        errNM += dx*dx + dy*dy;
        cnt++;
      }
    }
    errNM = cnt ? errNM / cnt : Infinity;
  }
  
  if (Tm) {
    const trgM = applyTransformToPts(srcAll, Tm, false, centroid);
    errM = 0;
    let cnt = 0;
    for (let i = 0; i < trgM.length; i++) {
      const a = trgM[i], b = puppetTemplate[i];
      if (!a || !b) continue;
      if ((a.v ?? 0) >= VISIBILITY_THRESHOLD) {
        const dx = a.x - b.x, dy = a.y - b.y;
        errM += dx*dx + dy*dy;
        cnt++;
      }
    }
    errM = cnt ? errM / cnt : Infinity;
  }

  // ✨ 改进：玻璃态镜像决策（防止频繁切换）
  if (!mirrorDecisionMade) {
    if (mirrorForced === true) {
      cachedMirrorDecision = true;
      mirrorDecisionMade = true;
      console.log('✓ Mirror forced: MIRRORED');
    } else if (mirrorForced === false) {
      cachedMirrorDecision = false;
      mirrorDecisionMade = true;
      console.log('✓ Mirror forced: NORMAL');
    } else {
      // ✨ 玻璃态：已镜像时需要 errNM < errM * 0.85 才能切换回正常
      //         已正常时需要 errM < errNM * 1.15 才能切换到镜像
      const shouldBeMirrored = cachedMirrorDecision 
        ? (errM < errNM * 0.85)  // 镜像状态下的切换阈值（更严格）
        : (errM < errNM * MIRROR_HYSTERESIS);  // 正常状态下的切换阈值
      
      const currentVote = shouldBeMirrored ? 'mirrored' : 'normal';
      
      if (currentVote === lastMirrorVote) {
        mirrorConsecutiveFrames++;
      } else {
        mirrorConsecutiveFrames = 1;
        lastMirrorVote = currentVote;
      }
      
      if (mirrorConsecutiveFrames >= MIRROR_FRAMES_THRESHOLD) {
        const oldDecision = cachedMirrorDecision;
        cachedMirrorDecision = (currentVote === 'mirrored');
        mirrorDecisionMade = true;
        
        if (oldDecision !== cachedMirrorDecision) {
          console.log(`✓ Mirror locked: ${cachedMirrorDecision ? 'MIRRORED' : 'NORMAL'} (errNM=${errNM.toFixed(1)}, errM=${errM.toFixed(1)}, ratio=${(errM/errNM).toFixed(2)})`);
        }
      }
    }
  } else if (mirrorDecisionMade && !mirrorForced) {
    // ✨ 已决策后，继续监控以便重新评估（但保持玻璃态）
    const shouldBeMirrored = cachedMirrorDecision 
      ? (errM < errNM * 0.85)
      : (errM < errNM * MIRROR_HYSTERESIS);
    
    const currentVote = shouldBeMirrored ? 'mirrored' : 'normal';
    
    if (currentVote !== lastMirrorVote) {
      mirrorConsecutiveFrames = 1;
      lastMirrorVote = currentVote;
    } else {
      mirrorConsecutiveFrames++;
    }
    
    // ✨ 只有在连续超过阈值两倍时才切换（更稳定）
    if (mirrorConsecutiveFrames >= MIRROR_FRAMES_THRESHOLD * 2) {
      const oldDecision = cachedMirrorDecision;
      cachedMirrorDecision = (currentVote === 'mirrored');
      
      if (oldDecision !== cachedMirrorDecision) {
        console.log(`⚠️ Mirror RE-LOCKED: ${cachedMirrorDecision ? 'MIRRORED' : 'NORMAL'}`);
        mirrorConsecutiveFrames = 0;
        lastMirrorVote = null;
      }
    }
  }

  const chosenT = cachedMirrorDecision ? Tm : Tnm;
  if (!chosenT) return srcLandmarks;

  // ✨ 保守的变换更新（头部比较敏感）
  if (!currentTransform) {
    currentTransform = chosenT;
  } else {
    const lerp = 0.12;  // 从 0.08 → 0.12（头部需要更快响应）
    currentTransform.scale = currentTransform.scale * (1 - lerp) + chosenT.scale * lerp;
    currentTransform.tx = currentTransform.tx * (1 - lerp) + chosenT.tx * lerp;
    currentTransform.ty = currentTransform.ty * (1 - lerp) + chosenT.ty * lerp;
    const delta = angDiff(chosenT.angle, currentTransform.angle);
    currentTransform.angle = currentTransform.angle + delta * lerp;
  }

  // ✨ 应用变换
  let out = applyTransformToPts(srcLandmarks, currentTransform, cachedMirrorDecision, centroid);
  
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

// ============ setup（只保留一个） ============
function setup() {
  const cnv = createCanvas(canvasWidth, canvasHeight);
  cnv.id('p5canvas');

  videoEl = createVideo();
  videoEl.size(canvasWidth, canvasHeight);
  videoEl.hide();

  // ✅ 关键：预加载视频以减少延迟
  videoEl.elt.muted = true;
  videoEl.elt.autoplay = true;
  videoEl.elt.playsInline = true;
  videoEl.elt.setAttribute('playsinline', '');
  videoEl.elt.preload = 'auto';
  videoEl.elt.buffered;

  const fileInput = document.getElementById('videoFile');
  fileInput.addEventListener('change', (e) => {
    const file = e.target.files[0];
    if (!file) return;
    trail = [];
    const url = URL.createObjectURL(file);
    
    videoEl.elt.pause();
    videoEl.elt.muted = true;
    videoEl.elt.playsInline = true;
    videoEl.elt.preload = 'auto';
    videoEl.elt.src = url;
    videoEl.elt.load();

    let loadAttempts = 0;
    const tryPlay = () => {
      loadAttempts++;
      if (videoEl.elt.readyState >= 2) {
        videoEl.elt.play().catch(err => {
          if (loadAttempts < 5) setTimeout(tryPlay, 200);
          console.warn('Autoplay blocked:', err);
        });
      } else if (loadAttempts < 5) {
        setTimeout(tryPlay, 200);
      }
    };
    
    videoEl.elt.onloadeddata = tryPlay;
    videoEl.elt.oncanplay = tryPlay;
    videoEl.elt.onprogress = tryPlay;
    
    // ✨ 关键：视频加载时，动态调整 canvas 尺寸以保持原始比例
    videoEl.elt.onloadedmetadata = () => {
      const vW = videoEl.elt.videoWidth;
      const vH = videoEl.elt.videoHeight;
      
      // 计算缩放比例（保持视频宽高比，最大宽度 1280）
      const maxWidth = 1280;
      if (vW > maxWidth) {
        canvasHeight = Math.round(maxWidth * (vH / vW));
        canvasWidth = maxWidth;
      } else {
        canvasWidth = vW;
        canvasHeight = vH;
      }
      
      console.log(`✓ Video size: ${vW}×${vH} → Canvas: ${canvasWidth}×${canvasHeight}`);
      
      // ✨ 调整 canvas 和 video 尺寸
      resizeCanvas(canvasWidth, canvasHeight);
      videoEl.size(canvasWidth, canvasHeight);
      
      tryPlay();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
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
        await videoEl.elt.play();
        videoEl.elt.muted = false;
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
    modelComplexity: 0,
    smoothLandmarks: false,
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

// ============ onPoseResults（只保留一个） ============
function onPoseResults(results) {
  const vW = (videoEl && videoEl.elt && videoEl.elt.videoWidth) ? videoEl.elt.videoWidth : canvasWidth;
  const vH = (videoEl && videoEl.elt && videoEl.elt.videoHeight) ? videoEl.elt.videoHeight : canvasHeight;
  const scaleX = canvasWidth / vW;
  const scaleY = canvasHeight / vH;

  if (results.poseLandmarks && results.poseLandmarks.length) {
    if (!smoothedLandmarks || smoothedLandmarks.length !== results.poseLandmarks.length) {
      smoothedLandmarks = results.poseLandmarks.map(lm => ({
        x: (lm.x ?? 0) * vW * scaleX,
        y: (lm.y ?? 0) * vH * scaleY,
        v: lm.visibility ?? 1
      }));
      historyBuffers = smoothedLandmarks.map(() => ({ xs: [], ys: [], vs: [] }));
      footPredictionBuffer = {};
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
        mirrorDecisionMade = false;
        mirrorConsecutiveFrames = 0;
        lastMirrorVote = null;
        cachedMirrorDecision = false;
      }
    }

    let finalLandmarks = smoothedLandmarks;
    if (enableAutoAlign && puppetTemplate) {
      finalLandmarks = alignToPuppet(smoothedLandmarks);
    }
    
    if (finalLandmarks && enableAutoAlign) {
      predictOccludedFeet();
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

// ✨ 改进：脚部遮挡预测（在对齐之后调用）
function predictOccludedFeet() {
  if (!smoothedLandmarks) return;

  // ✨ 左脚和右脚分别处理
  for (let side = 0; side < 2; side++) {
    const isLeft = (side === 0);
    const ankleIdx = isLeft ? 27 : 28;
    const heelIdx = isLeft ? 29 : 30;
    const footTipIdx = isLeft ? 31 : 32;
    const kneeIdx = isLeft ? 25 : 26;

    const ankle = smoothedLandmarks[ankleIdx];
    const heel = smoothedLandmarks[heelIdx];
    const footTip = smoothedLandmarks[footTipIdx];
    const knee = smoothedLandmarks[kneeIdx];

    // ✨ 只在脚跟或脚尖可见性低时预测
    const heelVis = heel?.v ?? 0;
    const footTipVis = footTip?.v ?? 0;

    if ((heelVis < 0.35 || footTipVis < 0.35) && ankle && knee && (ankle.v ?? 0) >= 0.3) {
      // 计算小腿方向向量
      const legDx = ankle.x - knee.x;
      const legDy = ankle.y - knee.y;
      const legLen = Math.sqrt(legDx * legDx + legDy * legDy);

      if (legLen > 5) {  // 有效的小腿长度
        // 脚部方向：沿着小腿方向
        const dirX = legDx / legLen;
        const dirY = legDy / legLen;
        
        // 脚部总长度（约为小腿长度的 35%）
        const footLen = legLen * 0.35;

        // ✨ 脚跟预测：踝部下方 30% 脚长距离
        if (heelVis < 0.35) {
          heel.x = ankle.x + dirX * footLen * 0.3;
          heel.y = ankle.y + dirY * footLen * 0.3;
          heel.v = 0.5;  // 设为低可见性（这是预测值）
        }

        // ✨ 脚尖预测：踝部下方 100% 脚长距离
        if (footTipVis < 0.35) {
          footTip.x = ankle.x + dirX * footLen;
          footTip.y = ankle.y + dirY * footLen;
          footTip.v = 0.5;  // 设为低可见性（这是预测值）
        }
      }
    }
  }
}

// ============ draw ============
function draw() {
  background(30);

  // ⚡ 根据帧跳过配置调用 pose.send
  if (poseReady && videoEl && videoEl.elt && videoEl.elt.readyState >= 2 && !pausedFreeze) {
    if (frameCounter % (POSE_SKIP_FRAMES + 1) === 0) {
      try { pose.send({image: videoEl.elt}); } catch (err) { console.error('pose.send:', err); }
    }
    frameCounter++;
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

  // ✨ 注释掉红线轨迹绘制
  /*
  noFill();
  strokeWeight(2);
  stroke(255, 0, 0, 200);
  beginShape();
  for (let i = 0; i < trail.length; i++) {
    vertex(trail[i].x, trail[i].y);
  }
  endShape();

  if (trail.length > 0) {
    fill(255,200,0);
    noStroke();
    ellipse(trail[trail.length - 1].x, trail[trail.length - 1].y, 10, 10);
  }
  */

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
    noStroke();
    fill(0, 255, 100, 150);
    for (let i = 0; i < setupPointIdx; i++) {
      const idx = CRITICAL_POINTS[i];
      const p = puppetTemplate[idx];
      if (p && (p.x || p.y)) {
        ellipse(p.x, p.y, 10, 10);
      }
    }
    
    stroke(255, 200, 0, 200);
    strokeWeight(1);
    line(mouseX - 15, mouseY, mouseX + 15, mouseY);
    line(mouseX, mouseY - 15, mouseX, mouseY + 15);
    
    noStroke();
    fill(255, 200, 0);
    textSize(14);
    textAlign(CENTER, BOTTOM);
    const currentPointName = CRITICAL_NAMES[setupPointIdx] || "done";
    text(`${setupPointIdx + 1}/${CRITICAL_POINTS.length}: Click to set ${currentPointName}`, width / 2, 20);
    
    fill(200, 200, 200);
    textSize(10);
    textAlign(LEFT, TOP);
    let yPos = height - 100;
    text('✓ Completed:', 10, yPos);
    for (let i = 0; i < Math.min(setupPointIdx, CRITICAL_NAMES.length); i++) {
      yPos += 12;
      text(`${i + 1}. ${CRITICAL_NAMES[i]}`, 15, yPos);
    }
    pop();
  }
}

// ============ 鼠标交互 ============
function mouseMoved() {
  if (!manualEditMode || !puppetTemplate) { manualHoverIndex = -1; return; }
  const { idx, d } = findNearestIndex(mouseX, mouseY, puppetTemplate);
  manualHoverIndex = (d < 30) ? idx : -1;
}

function mousePressed() {
  if (setupMode) {
    if (mouseX < 0 || mouseY < 0 || mouseX > width || mouseY > height) return;
    if (setupPointIdx >= CRITICAL_POINTS.length) return;
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

function mouseDragged() {
  if (!manualEditMode || !manualDragging || manualSelectedIdx < 0 || !puppetTemplate) return;
  puppetTemplate[manualSelectedIdx].x = constrain(mouseX, 0, width);
  puppetTemplate[manualSelectedIdx].y = constrain(mouseY, 0, height);
  boneLengths = POSE_CONNECTIONS.map(([a, b]) => {
    const A = puppetTemplate[a], B = puppetTemplate[b];
    return A && B ? dist(A.x, A.y, B.x, B.y) : null;
  });
}

function mouseReleased() {
  manualDragging = false;
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

  const row1 = document.createElement('div');
  row1.style.marginBottom = '8px';

  const label1 = document.createElement('span');
  label1.textContent = '📋 Template Setup:';
  label1.style.fontWeight = 'bold';
  label1.style.display = 'block';
  label1.style.marginBottom = '4px';
  row1.appendChild(label1);

  const freezeBtn = document.createElement('button');
  freezeBtn.textContent = '1. Auto Freeze';
  freezeBtn.style.marginRight = '6px';
  freezeBtn.style.marginBottom = '4px';
  freezeBtn.style.padding = '4px 6px';
  freezeBtn.style.background = '#445';
  freezeBtn.onclick = () => {
    if (!resultsForDraw?.poseLandmarks && !smoothedLandmarks) {
      alert('❌ No pose detected.');
      return;
    }
    const src = resultsForDraw?.poseLandmarks || smoothedLandmarks;
    puppetTemplate = copyLandmarks(src);
    boneLengths = POSE_CONNECTIONS.map(([a,b]) => {
      const A = puppetTemplate[a], B = puppetTemplate[b];
      return A && B ? dist(A.x, A.y, B.x, B.y) : null;
    });
    console.log('✓ Template frozen');
    alert('✓ Template frozen. Use Manual Edit to adjust.');
  };
  row1.appendChild(freezeBtn);

  const manualSetBtn = document.createElement('button');
  manualSetBtn.textContent = `2. Click-to-Set`;
  manualSetBtn.style.padding = '4px 6px';
  manualSetBtn.style.background = '#544';
  manualSetBtn.onclick = () => {
    if (!puppetTemplate) {
      puppetTemplate = Array(33).fill(null).map(() => ({ x: 0, y: 0, v: 1 }));
    }
    setupMode = !setupMode;
    if (setupMode) setupPointIdx = 0;
    manualSetBtn.style.background = setupMode ? '#655' : '#544';
    if (setupMode) {
      alert(`Click ${CRITICAL_POINTS.length} points: ${CRITICAL_NAMES.join(', ')}`);
    }
  };
  row1.appendChild(manualSetBtn);
  container.appendChild(row1);

  const row2 = document.createElement('div');
  row2.style.marginBottom = '8px';

  const alignToggle = document.createElement('button');
  alignToggle.textContent = `AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
  alignToggle.style.marginRight = '6px';
  alignToggle.style.padding = '4px 6px';
  alignToggle.style.background = enableAutoAlign ? '#4a4' : '#a44';
  alignToggle.onclick = () => {
    enableAutoAlign = !enableAutoAlign;
    alignToggle.textContent = `AutoAlign: ${enableAutoAlign ? 'ON' : 'OFF'}`;
    alignToggle.style.background = enableAutoAlign ? '#4a4' : '#a44';
  };
  row2.appendChild(alignToggle);

  const manualToggle = document.createElement('button');
  manualToggle.textContent = 'Manual Edit';
  manualToggle.style.padding = '4px 6px';
  manualToggle.style.background = '#545';
  manualToggle.onclick = () => {
    if (!puppetTemplate) {
      alert('❌ Set template first!');
      return;
    }
    manualEditMode = !manualEditMode;
    manualToggle.textContent = manualEditMode ? '✓ Editing' : 'Manual Edit';
    manualToggle.style.background = manualEditMode ? '#655' : '#545';
  };
  row2.appendChild(manualToggle);
  container.appendChild(row2);

  const row3 = document.createElement('div');
  const expBtn = document.createElement('button');
  expBtn.textContent = 'Export';
  expBtn.style.marginRight = '6px';
  expBtn.style.padding = '4px 6px';
  expBtn.style.background = '#445';
  expBtn.onclick = () => {
    if (!puppetTemplate) { alert('No template'); return; }
    const data = { puppetTemplate, boneLengths };
    const a = document.createElement('a');
    a.href = 'data:application/json;charset=utf-8,' + encodeURIComponent(JSON.stringify(data, null, 2));
    a.download = `puppet_${Date.now()}.json`;
    document.body.appendChild(a);
    a.click();
    a.remove();
  };
  row3.appendChild(expBtn);

  const impInput = document.createElement('input');
  impInput.type = 'file';
  impInput.accept = '.json';
  impInput.style.fontSize = '10px';
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
          alert('✓ Imported');
        }
      } catch (err) {
        alert('Error: ' + err.message);
      }
    };
    r.readAsText(f);
  };
  row3.appendChild(impInput);
  container.appendChild(row3);

  document.body.appendChild(container);
}

// ============ 快捷键 ============
window.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && setupMode) {
    setupMode = false;
    boneLengths = POSE_CONNECTIONS.map(([a,b]) => {
      const A = puppetTemplate[a], B = puppetTemplate[b];
      return A && B ? dist(A.x, A.y, B.x, B.y) : null;
    });
    mirrorDecisionMade = false;
    mirrorConsecutiveFrames = 0;
    lastMirrorVote = null;
    cachedMirrorDecision = false;
    console.log('✓ Setup complete');
  } else if (e.key === 'Escape') {
    if (setupMode) { setupMode = false; setupPointIdx = 0; }
    else if (manualEditMode) manualEditMode = false;
  } else if (e.key === 'r' || e.key === 'R') {
    mirrorDecisionMade = false;
    mirrorConsecutiveFrames = 0;
    lastMirrorVote = null;
    cachedMirrorDecision = false;
    console.log('✓ Mirror decision reset, re-evaluating...');
  } else if (e.key === 'm' || e.key === 'M') {
    // ✨ 新增：按 M 键强制锁定当前镜像状态
    mirrorForced = cachedMirrorDecision ? false : true;
    console.log(`✓ Mirror ${mirrorForced ? 'FORCED to MIRRORED' : 'AUTO (toggle)'}`);
  }
});
