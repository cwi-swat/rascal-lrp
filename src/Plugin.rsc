module Plugin

import util::IDE;
import lang::lrp::Syntax;
import ParseTree;

void main() {
  registerLanguage("LRP", "lrp", start[LRP](str src, loc org) {
    return parse(#start[LRP], src, org);
  });
}