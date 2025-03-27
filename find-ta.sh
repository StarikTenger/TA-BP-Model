template_file=$1
filename=$(basename -- "$template_file")
model_name="${filename%.*}"

path=tmp/$model_name
mkdir -p $path

cp ./*.tla $path/
cp TestBench.cfg $path/base_$model_name.cfg
cp TestBench.cfg $path/search_$model_name.cfg

# Base model

python3 template-gen.py --base --name base_$model_name $template_file >$path/base_$model_name.tla

tlc -dump dot $path/base_$model_name.dot $path/base_$model_name.tla > $path/base-tlc-output.txt

time_output=$(python3 calc-time.py $path/base_$model_name.dot)

python3 diagram-diag.py $path/base_$model_name.dot > $path/diagram.trd

# Search model

python3 template-gen.py --time $time_output --name search_$model_name $template_file >$path/search_$model_name.tla

tlc $path/search_$model_name.tla > $path/search-tlc-output.txt

echo "-------------------------------------------------------------------------" >> $path/diagram.trd
python3 diagram-diag.py $path/search-tlc-output.txt >> $path/diagram.trd

