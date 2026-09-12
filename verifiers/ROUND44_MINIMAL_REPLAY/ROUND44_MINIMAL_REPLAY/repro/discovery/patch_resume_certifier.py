#!/usr/bin/env python3
"""Patch one frozen exported certifier; never edits the main model generator.

Usage:
  python3 patch_resume_certifier.py EXPORT/mc_certify.cpp \
      --bind-partial OLD.tree --partial-model ORIGINAL_EXPORT/model.json
  # Recompile that exported source as usual.
  ./certify NEW.tree NODE_LIMIT [OLD.tree]

Legacy prefixes need an explicit model-binding sidecar. Patched runs create
the sidecar themselves. Every copied C is still rechecked with exact integers.
"""
from pathlib import Path
import argparse
import json
import re

MARKER = '// R44_EXACT_PREFIX_RESUME_V1'
BINDING_SUFFIX = '.model-binding'

CPP = r'''
// R44_EXACT_PREFIX_RESUME_V1
namespace resume_fs = std::filesystem;
long resume_reused_nodes=0, resume_reused_leaves=0, resume_reused_splits=0;
long resume_discarded_final_records=0, resume_input_lines=0;

// This is a collision-free serialization of the actual compiled exact model,
// including its root and UNIT.  It is not a filename-based model assertion.
std::string resume_exact_binding(){
 std::ostringstream s;
 s<<"R44_RESUME_BINDING_V1\n"<<EV<<' '<<EN<<' '<<EB<<'\n'<<UNIT<<'\n';
 auto line=[&s](const auto&v){for(size_t i=0;i<v.size();i++){if(i)s<<' ';s<<v[i];}s<<'\n';};
 line(erootlo);line(eroothi);s<<epairs.size()<<'\n';
 for(auto[i,j]:epairs)s<<i<<' '<<j<<'\n';
 s<<ebase.size()<<'\n';
 for(size_t i=0;i<ebase.size();i++){s<<erhs.at(i);for(auto z:ebase[i])s<<' '<<z;s<<'\n';}
 return s.str();
}
bool resume_same_path(const resume_fs::path&a,const resume_fs::path&b){
 if(resume_fs::weakly_canonical(resume_fs::absolute(a))==resume_fs::weakly_canonical(resume_fs::absolute(b)))return true;
 return resume_fs::exists(a)&&resume_fs::exists(b)&&resume_fs::equivalent(a,b);
}
void resume_check_paths(const std::string&output,const std::string&input){
 std::vector<resume_fs::path> outs={output,output+".model-binding"};
 if(resume_same_path(outs[0],outs[1]))throw std::runtime_error("output aliases its binding sidecar");
 if(!input.empty()){
  std::vector<resume_fs::path> ins={input,input+".model-binding"};
  for(const auto&a:outs)for(const auto&b:ins)
   if(resume_same_path(a,b))throw std::runtime_error("resume input/output paths alias (possibly by symlink or hard link)");
 }
}
void resume_validate_binding(const std::string&input,const std::string&expected){
 if(!resume_fs::is_regular_file(input))throw std::runtime_error("partial tree is not a regular file");
 const auto path=input+".model-binding";
 if(!resume_fs::is_regular_file(path)||resume_fs::file_size(path)!=expected.size())
  throw std::runtime_error("missing or different partial-tree exact model/root binding");
 std::ifstream in(path,std::ios::binary);
 if(!in)throw std::runtime_error("cannot open partial-tree model binding");
 std::string actual((std::istreambuf_iterator<char>(in)),std::istreambuf_iterator<char>());
 if(in.bad()||actual!=expected)throw std::runtime_error("partial tree belongs to a different exact model/root");
}
void resume_write_binding(const std::string&output,const std::string&binding){
 std::ofstream out(output+".model-binding",std::ios::binary|std::ios::trunc);
 if(!out)throw std::runtime_error("cannot create output model binding");
 out<<binding;out.flush();
 if(!out)throw std::runtime_error("cannot write output model binding");
}
[[noreturn]] void resume_bad_record(const std::string&reason){
 throw std::runtime_error("invalid partial-tree record at line "+std::to_string(resume_input_lines)+": "+reason);
}
void resume_prefix(const EBox&box,std::istream&in,std::ostream&out){
 std::string line;
 if(!std::getline(in,line)){
  if(in.bad()||!in.eof())throw std::runtime_error("partial-tree read error (not EOF)");
  refine(box,out);return;
 }
 resume_input_lines++;
 if(in.bad())throw std::runtime_error("partial-tree read error");
 // Native emitters end every committed record with '\n'.  A final record
 // without it is an interrupted write, even if its last integer looks valid.
 // Discard only here: true EOF, and this box has not yet been paid.
 if(in.eof()){
  resume_discarded_final_records++;refine(box,out);return;
 }
 std::istringstream row(line);std::string op,junk;
 if(!(row>>op))resume_bad_record("empty record");
 if(nodes>NODE_LIMIT||box.depth>155)throw std::runtime_error("unresolved resource limit while replaying prefix");
 if(op=="S"){
  int j;if(!(row>>j))resume_bad_record("missing/out-of-range split index");
  if(row>>junk)resume_bad_record("extra split tokens");
  auto children=split_box(box,j); // Exact index, midpoint, and grid checks.
  nodes++;resume_reused_nodes++;resume_reused_splits++;
  maxdepth=std::max(maxdepth,box.depth);
  out<<line<<'\n';if(!out)throw std::runtime_error("output write failed");
  resume_prefix(children.first,in,out);resume_prefix(children.second,in,out);
 }else if(op=="C"){
  int n;if(!(row>>n)||n<1||n>EB+4*(int)epairs.size())resume_bad_record("bad support count");
  Weights weights;weights.reserve(n);
  for(int i=0;i<n;i++){
   int j;long long w;
   if(!(row>>j>>w))resume_bad_record("missing/out-of-range weight");
   weights.emplace_back(j,w);
  }
  if(row>>junk)resume_bad_record("extra contradiction tokens");
  // Reject invalid indices, duplicate rows, nonpositive weights, and every
  // non-strict margin in the CURRENT exact model and CURRENT DFS box.
  if(contradiction_margin(box,weights)>=0)resume_bad_record("leaf is not a strict exact contradiction");
  nodes++;leaves++;resume_reused_nodes++;resume_reused_leaves++;
  maxdepth=std::max(maxdepth,box.depth);
  out<<line<<'\n';if(!out)throw std::runtime_error("output write failed");
 }else resume_bad_record("unknown/unpaid instruction "+op);
}
int main(int argc,char**argv){try{
 if(argc<2||argc>4)throw std::runtime_error("usage: certify OUTPUT [NODE_LIMIT [PARTIAL_TREE]]");
 if(argc>2){size_t used=0;std::string arg=argv[2];long limit=std::stol(arg,&used);
  if(used!=arg.size()||limit<=0)throw std::runtime_error("NODE_LIMIT must be a positive integer");NODE_LIMIT=limit;}
 const std::string output=argv[1],input=argc==4?argv[3]:"";
 resume_check_paths(output,input);
 const std::string binding=resume_exact_binding();std::ifstream in;
 if(!input.empty()){
  resume_validate_binding(input,binding);in.open(input,std::ios::binary);
  if(!in)throw std::runtime_error("cannot open partial tree");
 }
 // Model/root mismatch and every alias check happen before opening OUTPUT.
 resume_write_binding(output,binding);
 std::ofstream out(output,std::ios::binary|std::ios::trunc);
 if(!out)throw std::runtime_error("cannot open output tree");
 start=std::chrono::steady_clock::now();
 if(input.empty())refine(root_box(),out);
 else{
  resume_prefix(root_box(),in,out);
  // Do not discard a final torn record here: there is no unpaid box left.
  if(in.bad())throw std::runtime_error("partial-tree read error after root");
  if(in.peek()!=std::char_traits<char>::eof())throw std::runtime_error("unconsumed partial-tree tail");
 }
 if(nodes!=2*leaves-1)throw std::runtime_error("completed partition bookkeeping mismatch");
 out.flush();if(!out)throw std::runtime_error("output flush failed");
 double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"EXACT_GENERATION_DONE nodes="<<nodes<<" leaves="<<leaves<<" maxdepth="<<maxdepth
  <<" seconds="<<sec<<" open=0 reused_nodes="<<resume_reused_nodes<<" reused_leaves="<<resume_reused_leaves
  <<" reused_splits="<<resume_reused_splits<<" new_solves="<<solves
  <<" discarded_final_records="<<resume_discarded_final_records<<std::endl;
 }catch(const std::exception&e){std::cerr<<"FAIL "<<e.what()<<std::endl;return 1;}}
'''


def exact_binding(model_path):
    """Produce the same full integer serialization as the compiled C++ code."""
    data = json.loads(Path(model_path).read_text())
    nv = len(data['variables'])
    pairs, rows = data['pairs'], data['rows']
    nx = nv + len(pairs)
    roots = data['root_numerators']
    den = data['root_denominator']
    if not isinstance(den, int) or den <= 0 or len(roots) != 2 or any(len(r) != nv for r in roots):
        raise ValueError('Invalid exact model/root metadata')
    parts = ['R44_RESUME_BINDING_V1', f'{nv} {nx} {len(rows)}', str(den << 128)]
    for root in roots:
        if any(not isinstance(v, int) for v in root):
            raise ValueError('Noninteger root numerator')
        parts.append(' '.join(map(str, root)))
    parts.append(str(len(pairs)))
    for pair in pairs:
        if len(pair) != 2 or any(not isinstance(i, int) or not 0 <= i < nv for i in pair):
            raise ValueError('Invalid product dictionary')
        parts.append(' '.join(map(str, pair)))
    parts.append(str(len(rows)))
    for row in rows:
        values = [row['rhs']] + row['coefficients']
        if len(values) != nx + 1 or any(not isinstance(v, int) for v in values):
            raise ValueError('Invalid exact integer row')
        parts.append(' '.join(map(str, values)))
    return ('\n'.join(parts) + '\n').encode()


def patched_source(source):
    if MARKER in source:
        return source
    if source.count('int main(') != 1:
        raise ValueError('Expected exactly one frozen exported main()')
    if not re.search(r'\bNODE_LIMIT\s*=', source) or 'usage: certify OUTPUT' not in source:
        raise ValueError('Expected a frozen exported OUTPUT/NODE_LIMIT certifier, not the PLAN vendor template')
    if 'void refine(' not in source or 'contradiction_margin(' not in source:
        raise ValueError('Missing expected exact discovery functions')
    prefix = source[:source.index('int main(')]
    includes = ''.join(f'#include <{h}>\n' for h in ('sstream', 'filesystem', 'iterator') if f'#include <{h}>' not in prefix)
    return includes + prefix + CPP.lstrip('\n')


def write_once_or_equal(path, content):
    path = Path(path)
    if path.exists():
        if path.read_bytes() != content:
            raise ValueError(f'Refusing to overwrite a different existing file: {path}')
        return
    path.write_bytes(content)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path, help='Frozen exported mc_certify.cpp')
    ap.add_argument('--output', type=Path, help='Optional distinct patched source; default patches source with backup')
    ap.add_argument('--bind-partial', type=Path, help='Legacy S/C prefix to bind to its original exported model')
    ap.add_argument('--partial-model', type=Path, help='Original frozen model.json; defaults to the prefix directory/model.json')
    args = ap.parse_args()
    if args.partial_model and not args.bind_partial:
        ap.error('--partial-model requires --bind-partial')
    source = args.source.resolve(strict=True)
    original = source.read_text()
    patched = patched_source(original)
    destination = args.output.resolve() if args.output else source
    partial = None
    if args.bind_partial:
        partial = args.bind_partial.resolve(strict=True)
        if not partial.is_file():
            raise ValueError('Partial tree must be a regular file')
        partial_model = args.partial_model or partial.parent / 'model.json'
        previous = exact_binding(partial_model)
        current = exact_binding(source.parent / 'model.json')
        if previous != current:
            raise ValueError('Legacy prefix source model/root differs from the patched export')
        if partial == destination or partial == source:
            raise ValueError('Partial tree aliases a source/output C++ path')
        write_once_or_equal(str(partial) + BINDING_SUFFIX, previous)
    if destination == source and patched != original:
        write_once_or_equal(str(source) + '.pre_resume', original.encode())
    if destination != source and destination.exists() and destination.read_text() != patched:
        raise ValueError('Refusing to overwrite a different patched-source output')
    if not destination.exists() or destination.read_text() != patched:
        destination.write_text(patched)
    print(json.dumps({'status': 'R44_RESUME_PATCH_READY', 'source': str(destination),
                      'partial_binding': str(partial) + BINDING_SUFFIX if partial else None,
                      'acceptance': 'Run the original independent exact verifier on the completed output.'}))


if __name__ == '__main__':
    main()
