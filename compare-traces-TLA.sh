template_file=$1
filename=$(basename -- "$template_file")
model_name="${filename%.*}"

path=tmp/$model_name\_compare
mkdir -p $path

cp ./*.tla $path/
cp TestBench.cfg $path/base_$model_name.cfg
cp TestBench.cfg $path/alt_$model_name.cfg

# Base model

python3 template-gen.py --base --name base_$model_name $template_file >$path/base_$model_name.tla

tlc -dump dot $path/base_$model_name.dot $path/base_$model_name.tla > $path/base-tlc-output.txt

python3 diagram-diag.py $path/base_$model_name.dot > $path/diagram.trd

# Alternative model

python3 template-gen.py --alt --name alt_$model_name $template_file >$path/alt_$model_name.tla

tlc -dump dot $path/alt_$model_name.dot $path/alt_$model_name.tla > $path/alt-tlc-output.txt

echo "-------------------------------------------------------------------------" >> $path/diagram.trd
python3 diagram-diag.py $path/alt_$model_name.dot >> $path/diagram.trd

