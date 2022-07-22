const ORIGIN = "https://05ce-126-81-21-47.ngrok.io";

const HEADERS = {
  // Accept: "application/json",
  // "Content-Type": "application/json",
  // Origin: "http://www.fos.kuis.kyoto-u.ac.jp",
  // "Access-Control-Request-Private-Network": true,
  // "Content-Type": "application/json",
};

// 証明系の名前と導出木の根をサーバーに送信
// responseは導出木（つまり、演習問題の解答）
const getDerivationTree = async (proofSysName, root) => {
  try {
    const response = await fetch(ORIGIN, {
      method: "POST",
      headers: HEADERS,
      body: JSON.stringify({ proofSysName: proofSysName, root: root }),
    });
    return await response.json();
  } catch (err) {
    console.log(err);
    return err;
  }
};

const onStart = () => {
  // 証明系の名前を取得
  const anchors = document.getElementsByTagName("a");
  const anchorsArray = Array.prototype.slice.call(anchors);
  const proofSysName = anchorsArray.filter((elem) => {
    return elem.getAttribute("target") === "_blank";
  })[0].textContent;

  // 導出木を書き込むDOMを取得
  let textArea = document.getElementsByTagName("textarea")[0];

  // 導出木の根となる部分を取得
  const root = textArea.value;

  // サーバーから導出木を受け取り、textAreaの値を書き換え
  getDerivationTree(proofSysName, root).then((res) => {
    textArea.value = res.result;
  });
};

onStart();
