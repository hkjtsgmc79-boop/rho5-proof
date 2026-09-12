from pathlib import Path
from fractions import Fraction as Q
import copy,json
from _v42_bootstrap import ROOT,prepare,v41_api
import bound_protocol as bp
import transport_box as tb

def run():
 S=json.loads((prepare()['handoff']/'round51/REMAINING_SAMPLES64.json').read_text())
 src=S[3];box=src['box'];p=json.loads((ROOT/'certificates/port_03.json').read_text());c=json.loads((ROOT/'certificates/composed_03.json').read_text())
 controls=[]
 def reject(name,fn):
  try:fn()
  except (ValueError,AssertionError,TypeError,KeyError):controls.append(name);return
  raise AssertionError('Bad input was accepted: '+name)
 def corrupt(n,k,v):o=copy.deepcopy(n);o[k]=v;return o
 reject('wrong reported source root',lambda:bp.verify(box,corrupt(p,'reported_round51_root_sha256','0'*64),True))
 reject('wrong model',lambda:bp.verify(box,corrupt(p,'model_sha256','0'*64),True))
 reject('wrong box identity',lambda:bp.verify(box,corrupt(p,'box_sha256','0'*64),True))
 reject('wrong prefix identity',lambda:bp.verify(box,corrupt(p,'prefix_sha256','0'*64),True))
 reject('wrong rule identity',lambda:bp.verify(box,corrupt(p,'rule_identity','0'*64),True))
 reject('cached image injection',lambda:bp.verify(box,corrupt(p,'aux_image',[]),True))
 reject('caller supplied cost',lambda:bp.verify(box,corrupt(p,'cost','0'),True))
 reject('caller supplied centers',lambda:bp.verify(box,corrupt(p,'centers',[]),True))
 reject('invalid proof options',lambda:bp.verify(box,corrupt(p,'method','unchecked'),True))
 reject('arbitrary profile substitution',lambda:bp.endpoint(box,corrupt(src['partial_certificate'],'trace',{'profile':'UNKNOWN','waves':[],'terminal':{'kind':'O'}})))
 bad=copy.deepcopy(src['partial_certificate']);bad['trace']['waves'][0][0]['weights'][0][1]=-1
 reject('negative intermediate weight',lambda:bp.endpoint(box,bad))
 bad=copy.deepcopy(src['partial_certificate']);del bad['trace']['waves'][0][0]['direction']
 reject('incomplete intermediate bound',lambda:bp.endpoint(box,bad))
 bad=copy.deepcopy(c);del bad['children'][next(iter(bad['children']))]
 reject('missing one of 189 graphs',lambda:bp.verify(box,bad,True))
 reject('unpaid full parent',lambda:bp.verify(box,c,False))
 bad=copy.deepcopy(c);lab=next(k for k,v in bad['children'].items()if v['terminal']['kind']=='O');bad['children'][lab]['terminal']={'kind':'I'}
 reject('false conditional contradiction',lambda:bp.verify(box,bad,True))
 reject('naked graph proof as root',lambda:bp.verify(box,{'kind':'C','weights':[[0,1]]},True))
 vp,_,_=v41_api()
 reject('new wrapper cannot be read as old G41',lambda:vp.verify(box,c,allow_open=True))
 reject('floating interval endpoint',lambda:tb.I(0.0,1))
 reject('boolean interval endpoint',lambda:tb.I(False,1))
 reject('zero pivot division',lambda:tb.I(1,2)/tb.I(-1,1))
 reject('wrong B24 dimension',lambda:tb.load_box([['1','2']]*22))
 reject('unknown transport theorem',lambda:tb.port_for_orientation(tb.load_box([['1','1']]*24),[['0']*22]*4,'missing'))
 return dict(status='V42_NEGATIVE_CONTROLS_PASS',count=len(controls),controls=controls)
if __name__=='__main__':print(json.dumps(run()))
