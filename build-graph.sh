model_name=$1

echo $model_name

tlc -dump dot $model_name.dot $model_name.tla
python3 pretty-graph.py $model_name.dot $model_name.dot
dot -Tpng $model_name.dot > $model_name.png

mv $model_name.dot $model_name.png ./tmp/