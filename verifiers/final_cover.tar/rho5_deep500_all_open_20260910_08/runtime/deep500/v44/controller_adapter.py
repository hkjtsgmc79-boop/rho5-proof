"""Call only at an actual leaf reconstructed from the controller's own original root.
This does not traverse, trust, or edit a tree supplied merely by a reported path.
"""
from branch_protocol import verify
from v44_bootstrap import source,fs

def verify_at_actual_leaf(actual_box,actual_index,actual_path,parent,certificate):
 real=source.inherited.validate_box(actual_box)
 declared=source.inherited.validate_box(parent['box'])
 if real!=declared:raise ValueError('Certificate is not for this actual original box')
 if type(actual_index)is not int or actual_index!=parent['index']:raise ValueError('Wrong actual original index')
 if actual_path!=parent['path']:raise ValueError('Wrong actual original path')
 if fs.box_hash(real)!=parent['box_sha256']:raise ValueError('Wrong actual original box hash')
 # Never accept the partial mode when registering an original parent as paid.
 return verify(parent,certificate,allow_open=False,cross_check=True)
