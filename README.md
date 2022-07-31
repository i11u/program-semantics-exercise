# program-semantics-exercise

Chrome拡張機能として実装している。

## 手順

1. cloneした後、[ngrok](https://ngrok.com/)をダウンロードする。ターミナルで `./ngrok http 3000` を実行してサーバを立てる。

2. chrome-extension/derive.jsの `ORIGIN` を、ngrokでフォワーディングされたURLに置換する（要改善）。

3. [Chrome拡張機能の管理画面](chrome://extensions/)で、cloneしたディレクトリを（「パッケージ化されていない拡張機能を読み込む」ボタンから）読み込む。

4. [おすなば](https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/CoPL/)へ行き、問題のページに移ると、（導出システムが実装されている問題に関しては）導出木が描かれる。

## 対応している導出システム

- Nat
- CompareNat[1-3]
- EvalNatExp
- EvalML[1-4]
- EvalML1Err
- TypingML4（Q89まで）
