# FalCAuN
## インスコ

- kscript が動かない, depends で指定するパッケージ名の ArtifactID がおかしい？
```diff
- @file:DependsOn("net.maswag.falcaun.FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun.FalCAuN-matlab:1.0-SNAPSHOT")
+ @file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
```
- cwd を `./example/kscript` へ移動しないと動かない
- example と examples の違いは?
- mealy.main.kts だけ matlab なしで動くらしい
  - mealy_main が無いと言われて動かない...
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
  - pacemaker.main.kts は Model1_Sceneario1_Correct.slx のsimulinkのバージョンが最新(2024a以降)でないと動かないかも?
    - https://jp.mathworks.com/help/simulink/slref/simulinkpreferences.html
    - matlab の command window で `slprivate('showprefs')` を実行して
      Simulink Preferences->Model Files->Do not load models created with a newer version of simulink のチェックを外す
- ignore_matlab.sh で matlab を無視してビルドできそうに見えたが,
  これ使われてない? core 以下で実行しなければならない？

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
- STLの式の意味論の説明が欲しい


## Examples
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
