if [ ! -d .python ] ; then
    python3 -m venv .python
    ./.python/bin/pip install plotnine toposort pandas
fi

source .python/bin/activate

# disable turbo boost
sudo /bin/sh -c "/usr/bin/echo 1 > /sys/devices/system/cpu/intel_pstate/no_turbo"

echo "performance" | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor


echo "running verus_nr"
(cd verified && ../.python/bin/python ../bench.py)
cp verified/data.json data-verified.json

echo "running upstream comparison"
(cd upstream && ../.python/bin/python ../bench.py)
cp upstream/data.json data-upstream.json

echo "running ironsync comparison"
(cd ironsync && cargo bench)
cp ../ironsync-osdi2023/concurrency/node-replication/data.json data-ironsync.json


echo "ondemand" | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor

