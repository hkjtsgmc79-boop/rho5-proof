import copy,json
from graph_protocol import *

def run():
 s=json.loads((paths.ROOT/'inputs/diagnostics/audit_final/SAMPLE_CONTROLS.json').read_text())[0]
 cert=json.loads((paths.ROOT/'evidence/frontier_covers/sample_00.json').read_text());pa=parent_enclosure(s['box'])
 assert verify_cover(s['box'],cert)['status']=='COMPLETE_BOX_HIGH_EMPTY'
 tested=[]
 def reject(name,fn):
  try:fn()
  except(ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):tested.append(name);return
  raise AssertionError('Failed to reject '+name)
 for key,value in [('rule','UNKNOWN'),('rule_identity','0'*64),('box_sha256','0'*64),('model_sha256','0'*64)]:
  c=copy.deepcopy(cert);c[key]=value;reject(key,lambda c=c:verify_cover(s['box'],c))
 c=copy.deepcopy(cert);c['children'].pop(GRAPH_LABELS[-1]);reject('missing_chart',lambda:verify_cover(s['box'],c))
 c=copy.deepcopy(cert);c['children']['BAD']={'kind':'I'};reject('extra_chart',lambda:verify_cover(s['box'],c))
 label=next(k for k,v in cert['children'].items()if v['kind']=='C');rec=copy.deepcopy(cert['children'][label])
 bad=copy.deepcopy(rec);bad['weights'][0][1]=-1;reject('negative_weight',lambda:verify_child(pa,label,bad))
 bad=copy.deepcopy(rec);bad['weights'].append(copy.deepcopy(bad['weights'][0]));reject('duplicate_weight_row',lambda:verify_child(pa,label,bad))
 bad={'kind':'C','weights':[[999999,1]]};reject('unknown_physical_row',lambda:verify_child(pa,label,bad))
 reject('fake_interval_empty',lambda:verify_child(pa,label,{'kind':'I'}))
 reject('fake_alpha_port',lambda:verify_child(pa,label,{'kind':'A'}))
 reject('open_chart',lambda:verify_child(pa,label,{'kind':'O'}))
 reject('nonpositive_height_weight',lambda:verify_child(pa,label,{'kind':'H','weights':rec['weights'],'objective_weight':0}))
 reject('unknown_graph',lambda:verify_child(pa,'B1|N:H:H',{'kind':'I'}))
 bad=copy.deepcopy(s['box']);bad[0][0]=1.5;reject('floating_point_box',lambda:verify_cover(bad,cert))
 goodbox=json.loads((paths.ROOT/'controls/positive_safe_box.json').read_text());good=json.loads((paths.ROOT/'controls/positive_safe_cover.json').read_text())
 assert verify_cover(goodbox,good)['status']=='COMPLETE_BOX_ALPHA_SAFE'
 gl=next(k for k,v in good['children'].items()if v['kind']=='A')
 reject('gamma_high_physical_control_cannot_be_empty',lambda:verify_child(parent_enclosure(goodbox),gl,{'kind':'I'}))
 return {'bad_input_classes_rejected':len(tested),'names':tested}

if __name__=='__main__':print(json.dumps(run(),indent=2))
