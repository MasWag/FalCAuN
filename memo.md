# FalCAuN
## やりたい or 疑問
- バージョン固定したい
  - example/hscc2020 とか　example/rv2021 とかコミットを固定してビルドして実行するようにしたいかも
- kotlin のバージョンもなんかいい感じに固定したい
  - java 11 も含めて sdk 経由で入れさせる？
- ~~kscript の dependson の format とか javadoc のバグとかの問題は和賀さんの手元だと大丈夫だったんだろうか~~ だめだったらしい
  - ./utils/deploy_javadoc.sh とかあるが...?
- robustness って結局どういうこと?
- `signal(x)` の x が指すものって結局なんだろう, 引数の n 番目で良い?

## 名目
- FalCAuNのソースコードの調査 : 48人時
- 再利用性と保守性を高めるためのリファクタリング方針の査定 : 40人時

## インストール&実行
- kscript が動かない, depends で指定するパッケージ名の ArtifactID がおかしい？
  ```diff
  - @file:DependsOn("net.maswag.falcaun.FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun.FalCAuN-matlab:1.0-SNAPSHOT")
  + @file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
  ```
- kscript は cwd を `./example/kscript` へ移動しないと動かない
- mealy.main.kts だけ matlab なしで動くらしい
  - (SOLVED) mealy_main が無いと言われて動かない...
    ```
    % ./mealy.main.kts
    Exception in thread "main" java.lang.ClassNotFoundException: kscript.scriplet.Mealy_main
    at java.base/java.net.URLClassLoader.findClass(URLClassLoader.java:476)
    at java.base/java.lang.ClassLoader.loadClass(ClassLoader.java:594)
    at java.base/java.lang.ClassLoader.loadClass(ClassLoader.java:527)
    at Main_Mealy_main$Companion.main(Main_Mealy_main.kt:5)
    at Main_Mealy_main.main(Main_Mealy_main.kt)
    at java.base/jdk.internal.reflect.NativeMethodAccessorImpl.invoke0(Native Method)
    at java.base/jdk.internal.reflect.NativeMethodAccessorImpl.invoke(NativeMethodAccessorImpl.java:62)
    at java.base/jdk.internal.reflect.DelegatingMethodAccessorImpl.invoke(DelegatingMethodAccessorImpl.java:43)
    at java.base/java.lang.reflect.Method.invoke(Method.java:566)
    at org.jetbrains.kotlin.runner.AbstractRunner.run(runners.kt:70)
    at org.jetbrains.kotlin.runner.Main.run(Main.kt:183)
    at org.jetbrains.kotlin.runner.Main.main(Main.kt:193)
    [kscript] [ERROR] Execution of scriplet failed:
    [kscript] [ERROR] Command     : 'bash -c /home/hsaito/.sdkman/candidates/kotlin/current/bin/kotlin  -classpath '/home/hsaito/.m2/repository/net/maswag/falcaun/FalCAuN-core/1.0-SNAPSHOT/FalCAuN-core-1.0-SNAPSHOT.jar:/home/hsaito/.m2/repository/org/uma/jmetal/jmetal-core/5.9/jmetal-core-5.9.ja
    :
    tion-api/2.0.1.Final/validation-api-2.0.1.Final.jar:/home/hsaito/.cache/kscript/jar_2a8a68e6b3e4d7fcdf3309c279bc44ed/scriplet.jar:/home/hsaito/.sdkman/candidates/kotlin/current/lib/kotlin-script-runtime.jar' Main_Mealy_main '
    [kscript] [ERROR] Exit Code   : 1   
    [kscript] [ERROR]
    ```
  - **kotlin 2.0 では動かない！** kotlin 1.9 にダウングレードすべし
  - ~~kscript も最新だと ATS1 は動かなかった 3.1.0 でやっている~~
  - バージョン固定したほうがよい?

  - ATS2.kts が動かん
    ```
    [kscript] [ERROR] Stderr      : '/home/hsaito/.cache/kscript/jar_c6053954427e99c7c1e5692b49852e09/ATS2.kts:42:20: error: interface SignalMapper does not have constructors[nl]val signalMapper = SignalMapper()[nl]                   ^[nl]'
    ```
    - SimpleSignalMapper に書き換えたら動きはした

  - pacemaker.main.kts は Model1_Sceneario1_Correct.slx の simulink のバージョンが最新(2024a以降)でないと動かないかも?
    - https://jp.mathworks.com/help/simulink/slref/simulinkpreferences.html
    - matlab の command window で `slprivate('showprefs')` を実行して
      Simulink Preferences->Model Files->Do not load models created with a newer version of simulink のチェックを外す

- ignore_matlab.sh で matlab を無視してビルドできそうに見えたが,
  これ使われてない? core 以下で実行しなければならない？
  - そもそもパッケージ名が違う, 多分古いのでもう動かない
  - 内容としては matlab ディレクトリ以下を rm する感じ

- jupyter notebook
  - README にあるとおり, pip で jupyter と kotlin-jupyter-kernel を入れたら良い
  ~~- conda を入れる~~
    ~~- 直接condaに入れるんじゃなくて, 仮想環境を作ってライブラリ自体はpipで入れるようにしたほうがいいかも~~
    ~~- miniconda~~
      ~~- `export CONDA_CHANGEPS1=false` するとプロンプトが壊れなくて済む~~
  ~~- `conda install jupyter jupyterlab notebook` で jupyter を入れる~~
    - jupyter notebook がブラウザのキャッシュの問題で表示されなくなる問題がある https://github.com/jupyter/notebook/issues/7221
  ~~- `conda install -c jetbrains kotlin-jupyter-kernel` とかすると kotlin-kernel が入る~~
    - kotlin-jupyter-kernel は kotlin 2.0 でも問題なかった
  - `JAVA_HOME=$JAVA_HOME KOTLIN_JUPYTER_JAVA_OPTS="-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64" jupyter notebook Git/FalCAuN` とかで起動(書いてある)
    - JAVA_HOME と MATLAB のパスを通している
  - ログは端末に流れてくる

- javadoc
  - unnamed package みたいな表示しかない
  - `mvn javadoc:aggregate`, 動かん?
    - バージョンが古いと? @link 中の型引数 `<T>` がエラーになるバグがありそう
      - https://www.mail-archive.com/commits@mesos.apache.org/msg26303.html ?
  - gh-pages ブランチに手元でビルドした document を upload して deploy してそう
    - latest の circleCI はコケている

- ./falcaun のバイナリ, 動かないw
  - linux のときに java が jvm 以下に無くても, エラー処理がうまくいかずスルーされているバグがある
    - `find /usr/lib/jvm/java-1.21.0-openjdk* -name java -type f | head -n 1` で find で失敗しても, パイプした命令が成功するので if 文は true に評価されて, `Java 21 found at ` と表示される

- example/hscc2020/utils コマンドが変わっている
  ```diff
  - robodoc --src ./diffDate.sh --doc ./doc/diffDate.html --singledoc --html
  + robodoc --src ./diffDate.sh --doc ./doc/diffDate.html --singlefile --html
  ```
  - robodoc 自体は header のドキュメントをそれっぽく html へ展開してくれる

## 雑記
- example と examples の違いは?
  - examples の方はメンテされてない 放棄されている？

- STLの式の意味論の説明が欲しい
  - STL - LTL : atomic な条件式に signal がかける, 大小比較ができる ?
  - Globally と Eventually は □ や ♢ で表記されることもある STL 一般の文法
    - U(Until) で代用できるため論文中では定義されてなかった？
    - Eventually はなんで F があるのに Finally じゃないんだろ
    - これ `[]` は □, `<>` は ♢ のことか!
    - 多分 `[], alw, G` は全て同じ意味, EVENTUALLY も同様
  - interval について書いてない！
    - G や E で区間`[i,j]`を記述する際の文法
  - shellscript っぽく `$` をつけて書くと java の式を評価する機構がありそう (pacemaker.main.kts)

- example/kotlin/README.md
  - On macOS と On Linux の記述の仕方が非対称なので揃えたい
    ```
    After that, execute `jupyter` with suitable environmental variables. The following shows an example on macOS.
    :
    On Linux, you can likely find suitable directory to set `JAVA_HOME` by `ls /usr/lib/jvm/`.
    ```
- `.imap`, `.omap` はそれぞれ input mapper と output mapper ぽい

- 例を見たら十分かもしれないけれど, なんかチュートリアルか何かあれば良いんかな

## Examples
### kotlin
もしかして ATS1 って AT_S1 のことか？だとしたら ATS6 は何者？

- mealy.main.kts
  - 実行して最初に表示される画像のMealy型オートマトンに対し,
    2つのLTL条件式を満たすかBBCによって検査する例
- counter.ipynb
  - 正の入力をすると 1 を足し, 負の入力をすると 1 を引くシステム NumericSUL を定義
  - 出力に `mod 2` をした結果を STL 式で検証する
    - SignalMapper で出力を `mod 2` した値へ変換している
- pacemaker.main.kts
  - これなんやろ
- ATS1.main.kts
  - kotlin の use は closable の自動クローズをする構文 `SimulinkSUL(...).use { ...`
  - `"[] signal(3) < 20"` は, output の `val outputMapperReader = OutputMapperReader(listOf(ignoreValues, accelerationValues, gearValues, velocityValues))` の第3引数を指している?
  - ATS は AutoTransmissionShiftの略?
  - ATS1 は velocity, ATS2 は gear, ATS6 は acceleration の STL 式をチェックする例になっている
- ATS6a.main.kts
  - undocumented な stl 式の記述がある?
    - "$stlNotGRotationLt3000" で変数参照してそう
    - signalStep は多分グローバルな変数
    - U_interval の interval ってなんだ?
  - `val ignoreValues = listOf(null)` これなに？

### hscc2020
hscc2020 の実験で使ったコード.
- S1-S5 : ZESAH18
- M1-M2 : オリジナル

- run_falcaun.sh
  - これ mwaga マシンに依存してない?
    ```
    rm -f /home/mwaga/CyVeriA/src/test/resources/MATLAB/Autotrans_shift.mdl.autosave
    ```
    - 無くても問題ない?

- run_falcaun_all.sh
  - 一日かけても終わらんかった
  - 1.5日強で終了
  - table4_breach.stl のケースが動かない, `table4_breach.omap.tsv` が無い

### rv2021
四十坊さん作
- F1-F2 = S4-S5 : ZESAH18
- F3-F5 : オリジナル

### example 直下
CLI 用テスト
- S1-S2, S4-S5 : ZGS+18 (表記ゆれ)
- M3-M4 : オリジナル

- ./utils 以下の script の説明はここの README.md に書いてある

### examples 以下
- 古い
- org.group_mmm がもともとのパッケージのドメインだったっぽい どこかのタイミングで動いた
  - 2895e1ad56dcbccdb76b1e4dad3effa16fd01ca9

## コード読み
- System Under Learning(SUL) ~~って一般的な略語なんだろうか~~ は Learnlib 由来の略語?
  - Learnlib の wiki : https://github.com/LearnLib/learnlib/wiki/Instantiating-a-simple-learning-setup
- ANTLR v4 で TL 辺りのソースは一部自動生成されてる
- learnlib のドキュメントを見る限り, システムのオートマトンによる模倣メカニズムは Learnlib に依るものらしい
  - mapper もそう
  - cache = MembershipOracle?

- falcaun (script)
  - linux 版の java が `/usr/lib/jvm` 以下の java11 を探すようになっている
  - sdk 版だと違う場所
  - まずは JAVA_HOME から探したほうが良いのかも?

- LTSMin
  - ./utils/check_env.sh だと etf2lts-mc の存在だけ確認しているけれど,
    ソースではガッツリライブラリに依存している
  - LTSMonitorIOBuilder 使っている
    - LTSMonitorIO : MealyModelChecker のファクトリで, findCounterExample を実行すると条件式 (STL式) に違反しているmealyマシンとその入出力を返す
    - BlackBoxVerifier と AbstractAdaptiveUpdater で使用
    - https://learnlib.de/automatalib/maven-site/latest/apidocs/net/automatalib/modelchecker/ltsmin/monitor/package-summary.html
    - つまり, STL式に違反している入力を探すパートで使用している?

- SimulinkSULMapper -> NumericSULMapper のコミット : bff0a3fa13796c77fdc727ecdcb9edf84c80e0c8

### core
- `NumericSUL`
  -  `SUL` を継承
    - `SUL` は Learnlib
- `NumericSULVerifier`
  - `BlackBoxSUL` の wrapper
  - `getCexOutput()`
    - Input の方は `CexAbstractInput`, `CexConcreteInput` があり,
      もともと Output 版もあった模様
      - Abstract : Alphabet へ map した後の値
      - Concrete : map 前の実数値
    - 今のこれは Abstract の方を返す
- `RoSI`
  - robust satisfaction interval (RoSI)

- AbstractAdaptiveSTLUpdater
  - AdaptiveSTLUpdater の実装
  - AdaptiveSTLList, StaticSTLList, StaticLTLList が継承
  - Adaptive なんちゃらが多分四十坊さんの STL 式を書き換える機能を指している
  

#### Learnlib
- MembershipOracle
  - 対象システムの言語に, ある単語が属するか判定するクラスインターフェース
  - processQuery だけ 
- EquivalenceOracle
  - 対象システムとAMが一致するか判定するクラスインターフェース
  - findCounterExample だけ

### matlab
- `SimulinkSULVerifier`
  - `NumericSULVerifier` を継承
  - コンストラクタの `simulinkSimulationStep : double`, 何？
- `SimulinkModels.step(@Nonnull List<Double> inputSignal)`
  - 過去の inputSignal を全部保持して毎回一から実行してそう


## Thesis
### Falsification of Cyber-Physical Systems with Robustness Guided Black-Box Checking
- 23rd ACM International Conference on Hybrid Systems: Computation and Control (HSCC 2020)
- CPS(Cyber Physical System) のモデルがある仕様を満たすかどうかを
  Mealy Machine でエミュレートする BBC(Black-Box Checking) 手法でテストするツール FalCAuN を実装した
  - ある CPS モデル M が STL(Signal Temporal Logic, 線形時相論理 LTL の亜種?) の述語を満たすかどうかを,
    M と等価な Mealy Machine M' を学習によって構築し,
    M' に対してモデルチェック をすることで判定する 
    - モデルチェックが成功した場合, M と M' の等価性判定をして学習を回す
    - 失敗した場合, 反例が得られるのでそれを M に対して実行する
- 等価性判定が重い, 乱択か遺伝アルゴリズムか山登り法か
- 構築した Mealy Machine が学習に使った論理式に依存している問題がある

### Efficient Black-Box Checking via Model Checking with Strengthened Specifications
四十坊さん著
- 等価性判定を高速化してそう
