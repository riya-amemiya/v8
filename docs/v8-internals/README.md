# V8 内部型システム完全解説書

V8 (https://v8.dev/) の内部で JavaScript の値がどのように表現され、どのように処理されているのかを、ソースコードの該当箇所と引用を交えながら詳細に解説します。本書は登壇資料の参考文献として作成しました。

調査時点の V8 リビジョンは `/home/user/v8` のチェックアウトに準拠しています。ファイルパスと行番号は同リビジョン基準です。

## 目次

1. [Tagged Pointer と Smi - V8 における値の最小単位](./01-tagged-pointer-smi.md)
2. [HeapObject と Object 階層](./02-heap-object-hierarchy.md)
3. [Map (Hidden Class) と Transition Tree](./03-map-transitions.md)
4. [JSObject のレイアウトと Properties / Elements](./04-jsobject-layout.md)
5. [ElementsKind 完全列挙と遷移](./05-elements-kinds.md)
6. [String 階層 (SeqString / ConsString / SlicedString / ThinString / ExternalString)](./06-string-hierarchy.md)
7. [Number, HeapNumber, BigInt, Oddball](./07-number-bigint-oddball.md)
8. [Pointer Compression Cage と V8 Sandbox](./08-pointer-compression-sandbox.md)
9. [Heap Spaces とメモリレイアウト](./09-heap-spaces.md)
10. [Orinoco GC - Scavenger と Mark-Compact](./10-orinoco-gc.md)
11. [実行パイプライン - Ignition / Sparkplug / Maglev / TurboFan](./11-execution-pipeline.md)
12. [Inline Cache, Type Feedback, FeedbackVector](./12-inline-cache-feedback.md)

## 取り扱う領域の概要

V8 が「速い」と評される理由は、ひとつの大発明によるものではなく、多数の最適化の積み重ねによります。値の表現一つを取っても、Smi、HeapObject、Pointer Compression、Sandbox、Indirect Pointer など複数の仕組みが重なっています。オブジェクトレイアウトの面では Map (Hidden Class)、ElementsKind、in-object / out-of-object properties、Dictionary mode などの多段階の最適化があります。実行面では Ignition から TurboFan までの 4 段階の階層的コンパイラ、IC によるフィードバック駆動の最適化、そして Orinoco による低停止時間の GC が組み合わさっています。

本書はこれらをそれぞれ独立した章として解説しつつ、章をまたいだ参照を多用することで、全体像を立体的に把握できるよう構成しています。
