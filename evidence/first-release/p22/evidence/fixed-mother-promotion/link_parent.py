from pathlib import Path
src=Path('.lake/build/lib/lean/SaturationMonoid').resolve(); dst=Path('.cache/fixed-mother-promotion/SaturationMonoid'); count=0
def overlay(a,b):
 global count
 b.mkdir(parents=True,exist_ok=True)
 for x in a.iterdir():
  y=b/x.name
  if not y.exists(): y.symlink_to(x,target_is_directory=x.is_dir());count+=1
  elif x.is_dir() and y.is_dir() and not y.is_symlink():overlay(x,y)
overlay(src,dst)
print('UNCHANGED_PARENT_OVERLAY',count)
