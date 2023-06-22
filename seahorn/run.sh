for ((i=1;i<=133;i++)); do
	sea pf seahorn_benchmark/$i.c --cpu 10 > seahorn_output/$i.out
	echo $i
done
