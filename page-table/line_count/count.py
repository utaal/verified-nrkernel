counts="cat manual_count.txt | cut -f 1 -d '|' | sort | sed '/^# / d' | sed '/^ *$/ d' | uniq -c"

import subprocess
output = subprocess.check_output(counts, shell=True)
output = output.decode('utf-8')
counts = {}
for line in output.split('\n'):
    if line:
        count, name = line.split()
        names = name.split(',')
        for n in names:
            counts.setdefault(n, 0)
            counts[n] += int(count)

print(
"""HL Spec: {}
Trusted: {}
Spec and Proof: {}""".format(counts['HLSpec'], counts['Trusted'], counts['Spec'] + counts['Proof']))
