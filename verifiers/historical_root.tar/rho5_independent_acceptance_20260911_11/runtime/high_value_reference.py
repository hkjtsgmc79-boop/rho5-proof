"""Independent Fraction acceptance; missing tags preserve original V37 semantics."""
from interval_capacity import oracle as base_oracle
from high_value_contraction import oracle_from_base
from relaxation import verify_leaf as original_verify_leaf, margin
from native_backend import validate_record, ENCLOSURE

def oracle(box, *, local_ports=True):
    return oracle_from_base(base_oracle(box,local_ports=local_ports),local_ports=local_ports)

def verify_leaf(box,record):
    validate_record(record)
    if 'enclosure' not in record:return original_verify_leaf(box,record)
    if record['enclosure']!=ENCLOSURE:raise ValueError('unknown enclosure version')
    out=oracle(box)
    if record['kind']=='E':
        if out['status']=='OPEN':raise ValueError('uncertified high-value E')
        return out['status']
    if 'aux_image' not in out:raise ValueError('C/H needs canonical image')
    value=margin(out['aux_image'],record)
    if record['kind']=='C':
        if value>=0:raise ValueError('invalid high-value C margin')
        return 'EMPTY'
    if value>0:raise ValueError('invalid high-value H margin')
    return 'SAFE'
