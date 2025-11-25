// 全局变量与配置
let videoEl;
let pose;
let resultsForDraw = null;
let trail = [];
let selectedLandmark = 16; // 默认右手腕
const MAX_TRAIL = 200;
let playBtn;
let poseReady = false; // 添加：标记 pose 是否初始化完成

const LANDMARKS = [
  "nose","leftEyeInner","leftEye","leftEyeOuter","rightEyeInner","rightEye","rightEyeOuter",
  "leftEar","rightEar","mouthLeft","mouthRight","leftShoulder","rightShoulder","leftElbow","rightElbow",
  "leftWrist","rightWrist","leftPinky","rightPinky","leftIndex","rightIndex","leftThumb","rightThumb",
  "leftHip","rightHip","leftKnee","rightKnee","leftAnkle","rightAnkle","leftHeel","rightHeel","leftFootIndex","rightFootIndex"
];

// 添加身体连接关系（索引对应 LANDMARKS 顺序）
const POSE_CONNECTIONS = [
  // arms
  [11,13],[13,15],[12,14],[14,16],
  // shoulders / hips / torso
  [11,12],[11,23],[12,24],[23,24],
  // legs
  [23,25],[25,27],[24,26],[26,28],
  // lower legs -> feet
  [27,29],[29,31],[28,30],[30,32],
  // hands (wrist -> fingers)
  [15,17],[17,19],[19,21],[16,18],[18,20],[20,22],
  // face-ish connections (可选，增强可视化)
  [0,1],[1,3],[0,2],[2,4],[5,6],[5,7],[6,8],[7,9],[8,10]
];

function setup() {
  // 使用与原来相同的画布大小或根据需要调整
  const cnv = createCanvas(640, 480);
  cnv.id('p5canvas');

  // 创建隐藏 video 元素（用于送入 MediaPipe）
  videoEl = createVideo();
  videoEl.size(640, 480);
  videoEl.hide();

  // 文件选择绑定
  const fileInput = document.getElementById('videoFile');
  fileInput.addEventListener('change', (e) => {
    const file = e.target.files[0];
    if (!file) return;
    trail = [];
    const url = URL.createObjectURL(file);
    videoEl.elt.src = url;
    videoEl.elt.load();
    // 当元数据加载完成后，自动播放以触发处理
    videoEl.elt.onloadedmetadata = () => {
      videoEl.elt.play();
    };
  });

  // 填充关节点下拉
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
  playBtn.addEventListener('click', () => {
    if (!videoEl || !videoEl.elt) return;
    if (videoEl.elt.paused) videoEl.elt.play(); else videoEl.elt.pause();
  });

  // 初始化 MediaPipe Pose
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
  
  // 添加：初始化完成回调
  pose.initialize().then(() => {
    poseReady = true;
    console.log('MediaPipe Pose 初始化完成');
  }).catch((err) => {
    console.error('MediaPipe Pose 初始化失败:', err);
  });
}

function onPoseResults(results) {
  // 保存结果用于绘制
  resultsForDraw = results;

  // 将选定关节点坐标加入轨迹（屏幕坐标）
  if (results.poseLandmarks && results.poseLandmarks[selectedLandmark]) {
    const lm = results.poseLandmarks[selectedLandmark];
    // MediaPipe 返回相对坐标 (x,y) in [0,1], 左上为 (0,0)
    const x = lm.x * width;
    const y = lm.y * height;
    trail.push({x, y, score: lm.visibility ?? 1});
    if (trail.length > MAX_TRAIL) trail.shift();
  }
}

function draw() {
  background(30);

  // 修改：只有 pose 准备好且视频就绪才发送帧
  if (poseReady && videoEl && videoEl.elt && videoEl.elt.readyState >= 2) {
    try {
      pose.send({image: videoEl.elt});
    } catch (err) {
      console.error('pose.send 错误:', err);
    }
  }

  // 显示视频帧到 p5 画布（作为底图）
  if (videoEl && videoEl.elt && videoEl.elt.videoWidth > 0) {
    push();
    image(videoEl, 0, 0, width, height);
    pop();
  }

  // 如果有检测结果，先绘制骨架连线，再绘制关键点
  if (resultsForDraw && resultsForDraw.poseLandmarks) {
    // 绘制骨架连线
    stroke(0, 200, 255, 220);
    strokeWeight(3);
    for (let i = 0; i < POSE_CONNECTIONS.length; i++) {
      const [aIdx, bIdx] = POSE_CONNECTIONS[i];
      const a = resultsForDraw.poseLandmarks[aIdx];
      const b = resultsForDraw.poseLandmarks[bIdx];
      if (!a || !b) continue;
      line(a.x * width, a.y * height, b.x * width, b.y * height);
    }

    // 绘制所有关键点小圆点
    noStroke();
    fill(0, 255, 0);
    for (let i = 0; i < resultsForDraw.poseLandmarks.length; i++) {
      const lm = resultsForDraw.poseLandmarks[i];
      const px = lm.x * width;
      const py = lm.y * height;
      ellipse(px, py, 6, 6);
    }
  }

  // 绘制轨迹
  noFill();
  strokeWeight(2);
  stroke(255, 0, 0, 200);
  beginShape();
  for (let i = 0; i < trail.length; i++) {
    const p = trail[i];
    vertex(p.x, p.y);
  }
  endShape();

  // 绘制当前点高亮
  if (trail.length > 0) {
    const p = trail[trail.length - 1];
    fill(255, 200, 0);
    noStroke();
    ellipse(p.x, p.y, 10, 10);
  }
}
