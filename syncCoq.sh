rsync -av --delete --exclude="asts" --exclude="**/#*" --exclude="**/*~" --exclude="**/.lia.cache" --exclude="**/.nia.cache" /home/abhishek/work/coq/blue/fm-workspace-snapshot3b/fm-workspace-12-16/monad/ monadproofs/
git add monadproofs
chmod -R -w monadproofs
#rsync -av --delete --exclude="**/#*" --exclude="**/*~" --exclude="**/.lia.cache" --exclude="**/.nia.cache" /home/abhishek/work/coq/blue/fm-workspace-snapshot3b/fm-workspace-12-16/fmdeps/evm-op-sem/ evm-op-sem/
#git add monadproofs
#git add evm-op-sem

