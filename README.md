The ONE Simulator(https://akeranen.github.io/the-one/) 上に地形の情報を利用してメッセージの複製の判断を行うルーティング手法, CD-PRoPHETおよびLog-PRoPHETの実装を行った. <br>
シミュレーションの際にエージェントのルーティング手法としてCD-PRoPHETおよびLog-PRoPHETを選択することでそれぞれの手法をシミュレーションすることができる. <br>
シミュレータの基本的な使用方法はThe ONE Simulatorのページを参照. <br>

使用する際には, それぞれのroutingのファイルだけでなく, DTNHost, Coordも改変されていることに注意してください. 

reportsフォルダにはシミュレーションの結果を格納している. "Log-PRoPHET"については, 結果ファイルが仮名称の"ProphetWait"になっている.<br>
PRoPHET, CD-PRoPHETについては"ルーティング手法/TTL/エージェント数", Log-PRoPHETでは"ルーティング手法/TTL/移動履歴の保持数/エージェント数/メッセージの複製を制限する類似度の閾値"というフォルダ構造になっている.<br>
