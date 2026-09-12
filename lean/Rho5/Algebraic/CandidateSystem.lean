import Rho5.Algebraic.Core

noncomputable section
namespace Rho5.Algebraic

set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Literal integer polynomials from the supplied p1.txt, p2.txt, p3.txt.
Their 169/216/193 monomials are not replaced by an assumed equivalent system. -/

def p1Poly : Poly :=
    4 * xVar^6 * yVar^2 * zVar^6
     + 4 * xVar^6 * yVar^2 * zVar^5
     + 4 * xVar^6 * yVar * zVar^7
     - 12 * xVar^6 * yVar * zVar^5
     - 8 * xVar^6 * yVar * zVar^4
     - 4 * xVar^6 * zVar^7
     - 4 * xVar^6 * zVar^6
     + 16 * xVar^5 * yVar^2 * zVar^7
     + 20 * xVar^5 * yVar^2 * zVar^6
     - 20 * xVar^5 * yVar^2 * zVar^5
     - 24 * xVar^5 * yVar^2 * zVar^4
     + 12 * xVar^5 * yVar * zVar^8
     + 8 * xVar^5 * yVar * zVar^7
     - 52 * xVar^5 * yVar * zVar^6
     - 48 * xVar^5 * yVar * zVar^5
     + 32 * xVar^5 * yVar * zVar^4
     + 32 * xVar^5 * yVar * zVar^3
     - 8 * xVar^5 * zVar^8
     - 20 * xVar^5 * zVar^7
     + 4 * xVar^5 * zVar^6
     + 16 * xVar^5 * zVar^5
     + 25 * xVar^4 * yVar^2 * zVar^8
     + 39 * xVar^4 * yVar^2 * zVar^7
     - 53 * xVar^4 * yVar^2 * zVar^6
     - 99 * xVar^4 * yVar^2 * zVar^5
     + 12 * xVar^4 * yVar^2 * zVar^4
     + 44 * xVar^4 * yVar^2 * zVar^3
     + 13 * xVar^4 * yVar * zVar^9
     + 22 * xVar^4 * yVar * zVar^8
     - 70 * xVar^4 * yVar * zVar^7
     - 124 * xVar^4 * yVar * zVar^6
     + 69 * xVar^4 * yVar * zVar^5
     + 158 * xVar^4 * yVar * zVar^4
     + 4 * xVar^4 * yVar * zVar^3
     - 40 * xVar^4 * yVar * zVar^2
     - 5 * xVar^4 * zVar^9
     - 27 * xVar^4 * zVar^8
     - 15 * xVar^4 * zVar^7
     + 55 * xVar^4 * zVar^6
     + 28 * xVar^4 * zVar^5
     - 20 * xVar^4 * zVar^4
     + 2 * xVar^3 * yVar^3 * zVar^6
     - 2 * xVar^3 * yVar^3 * zVar^4
     + 19 * xVar^3 * yVar^2 * zVar^9
     + 37 * xVar^3 * yVar^2 * zVar^8
     - 49 * xVar^3 * yVar^2 * zVar^7
     - 141 * xVar^3 * yVar^2 * zVar^6
     - 14 * xVar^3 * yVar^2 * zVar^5
     + 136 * xVar^3 * yVar^2 * zVar^4
     + 52 * xVar^3 * yVar^2 * zVar^3
     - 24 * xVar^3 * yVar^2 * zVar^2
     + 6 * xVar^3 * yVar * zVar^10
     + 21 * xVar^3 * yVar * zVar^9
     - 32 * xVar^3 * yVar * zVar^8
     - 138 * xVar^3 * yVar * zVar^7
     + 12 * xVar^3 * yVar * zVar^6
     + 257 * xVar^3 * yVar * zVar^5
     + 86 * xVar^3 * yVar * zVar^4
     - 140 * xVar^3 * yVar * zVar^3
     - 56 * xVar^3 * yVar * zVar^2
     + 16 * xVar^3 * yVar * zVar
     - xVar^3 * zVar^10
     - 13 * xVar^3 * zVar^9
     - 27 * xVar^3 * zVar^8
     + 33 * xVar^3 * zVar^7
     + 88 * xVar^3 * zVar^6
     - 20 * xVar^3 * zVar^5
     - 52 * xVar^3 * zVar^4
     + 8 * xVar^3 * zVar^3
     + 5 * xVar^2 * yVar^3 * zVar^7
     + xVar^2 * yVar^3 * zVar^6
     - 13 * xVar^2 * yVar^3 * zVar^5
     - xVar^2 * yVar^3 * zVar^4
     + 8 * xVar^2 * yVar^3 * zVar^3
     + 7 * xVar^2 * yVar^2 * zVar^10
     + 17 * xVar^2 * yVar^2 * zVar^9
     - 18 * xVar^2 * yVar^2 * zVar^8
     - 83 * xVar^2 * yVar^2 * zVar^7
     - 46 * xVar^2 * yVar^2 * zVar^6
     + 106 * xVar^2 * yVar^2 * zVar^5
     + 137 * xVar^2 * yVar^2 * zVar^4
     - 20 * xVar^2 * yVar^2 * zVar^3
     - 60 * xVar^2 * yVar^2 * zVar^2
     + xVar^2 * yVar * zVar^11
     + 8 * xVar^2 * yVar * zVar^10
     - 63 * xVar^2 * yVar * zVar^8
     - 46 * xVar^2 * yVar * zVar^7
     + 155 * xVar^2 * yVar * zVar^6
     + 161 * xVar^2 * yVar * zVar^5
     - 112 * xVar^2 * yVar * zVar^4
     - 156 * xVar^2 * yVar * zVar^3
     + 4 * xVar^2 * yVar * zVar^2
     + 32 * xVar^2 * yVar * zVar
     - 2 * xVar^2 * zVar^10
     - 11 * xVar^2 * zVar^9
     - 3 * xVar^2 * zVar^8
     + 55 * xVar^2 * zVar^7
     + 41 * xVar^2 * zVar^6
     - 72 * xVar^2 * zVar^5
     - 40 * xVar^2 * zVar^4
     + 24 * xVar^2 * zVar^3
     + 4 * xVar * yVar^3 * zVar^8
     + 2 * xVar * yVar^3 * zVar^7
     - 16 * xVar * yVar^3 * zVar^6
     - 6 * xVar * yVar^3 * zVar^5
     + 20 * xVar * yVar^3 * zVar^4
     + 4 * xVar * yVar^3 * zVar^3
     - 8 * xVar * yVar^3 * zVar^2
     + xVar * yVar^2 * zVar^11
     + 3 * xVar * yVar^2 * zVar^10
     - 2 * xVar * yVar^2 * zVar^9
     - 17 * xVar * yVar^2 * zVar^8
     - 24 * xVar * yVar^2 * zVar^7
     + 12 * xVar * yVar^2 * zVar^6
     + 85 * xVar * yVar^2 * zVar^5
     + 50 * xVar * yVar^2 * zVar^4
     - 72 * xVar * yVar^2 * zVar^3
     - 52 * xVar * yVar^2 * zVar^2
     + 8 * xVar * yVar^2 * zVar
     + xVar * yVar * zVar^11
     + 2 * xVar * yVar * zVar^10
     - 9 * xVar * yVar * zVar^9
     - 22 * xVar * yVar * zVar^8
     + 25 * xVar * yVar * zVar^7
     + 82 * xVar * yVar * zVar^6
     - xVar * yVar * zVar^5
     - 106 * xVar * yVar * zVar^4
     - 48 * xVar * yVar * zVar^3
     + 36 * xVar * yVar * zVar^2
     + 24 * xVar * yVar * zVar
     - xVar * zVar^10
     - 3 * xVar * zVar^9
     + 7 * xVar * zVar^8
     + 27 * xVar * zVar^7
     - 6 * xVar * zVar^6
     - 52 * xVar * zVar^5
     - 4 * xVar * zVar^4
     + 24 * xVar * zVar^3
     + yVar^3 * zVar^9
     + yVar^3 * zVar^8
     - 5 * yVar^3 * zVar^7
     - 5 * yVar^3 * zVar^6
     + 8 * yVar^3 * zVar^5
     + 8 * yVar^3 * zVar^4
     - 4 * yVar^3 * zVar^3
     - 4 * yVar^3 * zVar^2
     - 2 * yVar^2 * zVar^8
     - 6 * yVar^2 * zVar^7
     + 8 * yVar^2 * zVar^6
     + 30 * yVar^2 * zVar^5
     - 2 * yVar^2 * zVar^4
     - 40 * yVar^2 * zVar^3
     - 12 * yVar^2 * zVar^2
     + 8 * yVar^2 * zVar
     - yVar * zVar^9
     - yVar * zVar^8
     + 7 * yVar * zVar^7
     + 11 * yVar * zVar^6
     - 10 * yVar * zVar^5
     - 26 * yVar * zVar^4
     - 4 * yVar * zVar^3
     + 16 * yVar * zVar^2
     + 8 * yVar * zVar
     + 2 * zVar^8
     + 4 * zVar^7
     - 6 * zVar^6
     - 12 * zVar^5
     + 4 * zVar^4
     + 8 * zVar^3

def p2Poly : Poly :=
    4 * xVar^7 * yVar^2 * zVar^6
     + 4 * xVar^7 * yVar^2 * zVar^5
     + 4 * xVar^7 * yVar * zVar^7
     - 4 * xVar^7 * yVar * zVar^5
     - 4 * xVar^7 * zVar^7
     - 4 * xVar^7 * zVar^6
     + 20 * xVar^6 * yVar^2 * zVar^7
     + 24 * xVar^6 * yVar^2 * zVar^6
     - 20 * xVar^6 * yVar^2 * zVar^5
     - 24 * xVar^6 * yVar^2 * zVar^4
     + 16 * xVar^6 * yVar * zVar^8
     + 8 * xVar^6 * yVar * zVar^7
     - 40 * xVar^6 * yVar * zVar^6
     - 8 * xVar^6 * yVar * zVar^5
     + 24 * xVar^6 * yVar * zVar^4
     - 12 * xVar^6 * zVar^8
     - 24 * xVar^6 * zVar^7
     + 12 * xVar^6 * zVar^6
     + 24 * xVar^6 * zVar^5
     + 41 * xVar^5 * yVar^2 * zVar^8
     + 59 * xVar^5 * yVar^2 * zVar^7
     - 73 * xVar^5 * yVar^2 * zVar^6
     - 123 * xVar^5 * yVar^2 * zVar^5
     + 20 * xVar^5 * yVar^2 * zVar^4
     + 52 * xVar^5 * yVar^2 * zVar^3
     + 25 * xVar^5 * yVar * zVar^9
     + 30 * xVar^5 * yVar * zVar^8
     - 96 * xVar^5 * yVar * zVar^7
     - 78 * xVar^5 * yVar * zVar^6
     + 123 * xVar^5 * yVar * zVar^5
     + 48 * xVar^5 * yVar * zVar^4
     - 52 * xVar^5 * yVar * zVar^3
     - 13 * xVar^5 * zVar^9
     - 47 * xVar^5 * zVar^8
     + 5 * xVar^5 * zVar^7
     + 111 * xVar^5 * zVar^6
     + 20 * xVar^5 * zVar^5
     - 52 * xVar^5 * zVar^4
     + 2 * xVar^4 * yVar^3 * zVar^6
     - 2 * xVar^4 * yVar^3 * zVar^4
     + 44 * xVar^4 * yVar^2 * zVar^9
     + 76 * xVar^4 * yVar^2 * zVar^8
     - 104 * xVar^4 * yVar^2 * zVar^7
     - 238 * xVar^4 * yVar^2 * zVar^6
     + 16 * xVar^4 * yVar^2 * zVar^5
     + 210 * xVar^4 * yVar^2 * zVar^4
     + 44 * xVar^4 * yVar^2 * zVar^3
     - 48 * xVar^4 * yVar^2 * zVar^2
     + 19 * xVar^4 * yVar * zVar^10
     + 43 * xVar^4 * yVar * zVar^9
     - 90 * xVar^4 * yVar * zVar^8
     - 184 * xVar^4 * yVar * zVar^7
     + 167 * xVar^4 * yVar * zVar^6
     + 245 * xVar^4 * yVar * zVar^5
     - 144 * xVar^4 * yVar * zVar^4
     - 104 * xVar^4 * yVar * zVar^3
     + 48 * xVar^4 * yVar * zVar^2
     - 6 * xVar^4 * zVar^10
     - 40 * xVar^4 * zVar^9
     - 32 * xVar^4 * zVar^8
     + 142 * xVar^4 * zVar^7
     + 146 * xVar^4 * zVar^6
     - 150 * xVar^4 * zVar^5
     - 108 * xVar^4 * zVar^4
     + 48 * xVar^4 * zVar^3
     + 5 * xVar^3 * yVar^3 * zVar^7
     + 3 * xVar^3 * yVar^3 * zVar^6
     - 13 * xVar^3 * yVar^3 * zVar^5
     - 3 * xVar^3 * yVar^3 * zVar^4
     + 8 * xVar^3 * yVar^3 * zVar^3
     + 26 * xVar^3 * yVar^2 * zVar^10
     + 54 * xVar^3 * yVar^2 * zVar^9
     - 72 * xVar^3 * yVar^2 * zVar^8
     - 224 * xVar^3 * yVar^2 * zVar^7
     - 30 * xVar^3 * yVar^2 * zVar^6
     + 270 * xVar^3 * yVar^2 * zVar^5
     + 184 * xVar^3 * yVar^2 * zVar^4
     - 104 * xVar^3 * yVar^2 * zVar^3
     - 96 * xVar^3 * yVar^2 * zVar^2
     + 16 * xVar^3 * yVar^2 * zVar
     + 7 * xVar^3 * yVar * zVar^11
     + 29 * xVar^3 * yVar * zVar^10
     - 30 * xVar^3 * yVar * zVar^9
     - 176 * xVar^3 * yVar * zVar^8
     + 44 * xVar^3 * yVar * zVar^7
     + 376 * xVar^3 * yVar * zVar^6
     - 45 * xVar^3 * yVar * zVar^5
     - 325 * xVar^3 * yVar * zVar^4
     + 40 * xVar^3 * yVar * zVar^3
     + 96 * xVar^3 * yVar * zVar^2
     - 16 * xVar^3 * yVar * zVar
     - xVar^3 * zVar^11
     - 15 * xVar^3 * zVar^10
     - 36 * xVar^3 * zVar^9
     + 56 * xVar^3 * zVar^8
     + 197 * xVar^3 * zVar^7
     - 45 * xVar^3 * zVar^6
     - 300 * xVar^3 * zVar^5
     + 8 * xVar^3 * zVar^4
     + 128 * xVar^3 * zVar^3
     - 16 * xVar^3 * zVar^2
     + 4 * xVar^2 * yVar^3 * zVar^8
     + 7 * xVar^2 * yVar^3 * zVar^7
     - 15 * xVar^2 * yVar^3 * zVar^6
     - 19 * xVar^2 * yVar^3 * zVar^5
     + 19 * xVar^2 * yVar^3 * zVar^4
     + 12 * xVar^2 * yVar^3 * zVar^3
     - 8 * xVar^2 * yVar^3 * zVar^2
     + 8 * xVar^2 * yVar^2 * zVar^11
     + 20 * xVar^2 * yVar^2 * zVar^10
     - 24 * xVar^2 * yVar^2 * zVar^9
     - 108 * xVar^2 * yVar^2 * zVar^8
     - 38 * xVar^2 * yVar^2 * zVar^7
     + 150 * xVar^2 * yVar^2 * zVar^6
     + 178 * xVar^2 * yVar^2 * zVar^5
     - 6 * xVar^2 * yVar^2 * zVar^4
     - 172 * xVar^2 * yVar^2 * zVar^3
     - 56 * xVar^2 * yVar^2 * zVar^2
     + 48 * xVar^2 * yVar^2 * zVar
     + xVar^2 * yVar * zVar^12
     + 9 * xVar^2 * yVar * zVar^11
     + 2 * xVar^2 * yVar * zVar^10
     - 72 * xVar^2 * yVar * zVar^9
     - 47 * xVar^2 * yVar * zVar^8
     + 220 * xVar^2 * yVar * zVar^7
     + 129 * xVar^2 * yVar * zVar^6
     - 309 * xVar^2 * yVar * zVar^5
     - 117 * xVar^2 * yVar * zVar^4
     + 184 * xVar^2 * yVar * zVar^3
     + 32 * xVar^2 * yVar * zVar^2
     - 32 * xVar^2 * yVar * zVar
     - 2 * xVar^2 * zVar^11
     - 12 * xVar^2 * zVar^10
     - 2 * xVar^2 * zVar^9
     + 84 * xVar^2 * zVar^8
     + 74 * xVar^2 * zVar^7
     - 188 * xVar^2 * zVar^6
     - 174 * xVar^2 * zVar^5
     + 164 * xVar^2 * zVar^4
     + 104 * xVar^2 * zVar^3
     - 48 * xVar^2 * zVar^2
     + xVar * yVar^3 * zVar^9
     + 5 * xVar * yVar^3 * zVar^8
     - 3 * xVar * yVar^3 * zVar^7
     - 21 * xVar * yVar^3 * zVar^6
     + 2 * xVar * yVar^3 * zVar^5
     + 28 * xVar * yVar^3 * zVar^4
     - 12 * xVar * yVar^3 * zVar^2
     + xVar * yVar^2 * zVar^12
     + 3 * xVar * yVar^2 * zVar^11
     - 3 * xVar * yVar^2 * zVar^10
     - 25 * xVar * yVar^2 * zVar^9
     - 14 * xVar * yVar^2 * zVar^8
     + 46 * xVar * yVar^2 * zVar^7
     + 52 * xVar * yVar^2 * zVar^6
     + 20 * xVar * yVar^2 * zVar^5
     - 40 * xVar * yVar^2 * zVar^4
     - 96 * xVar * yVar^2 * zVar^3
     + 48 * xVar * yVar^2 * zVar
     + xVar * yVar * zVar^12
     + 2 * xVar * yVar * zVar^11
     - 10 * xVar * yVar * zVar^10
     - 25 * xVar * yVar * zVar^9
     + 40 * xVar * yVar * zVar^8
     + 97 * xVar * yVar * zVar^7
     - 83 * xVar * yVar * zVar^6
     - 154 * xVar * yVar * zVar^5
     + 88 * xVar * yVar * zVar^4
     + 96 * xVar * yVar * zVar^3
     - 36 * xVar * yVar * zVar^2
     - 16 * xVar * yVar * zVar
     - xVar * zVar^11
     - 3 * xVar * zVar^10
     + 9 * xVar * zVar^9
     + 35 * xVar * zVar^8
     - 16 * xVar * zVar^7
     - 112 * xVar * zVar^6
     - 4 * xVar * zVar^5
     + 132 * xVar * zVar^4
     + 16 * xVar * zVar^3
     - 48 * xVar * zVar^2
     + yVar^3 * zVar^9
     + yVar^3 * zVar^8
     - 5 * yVar^3 * zVar^7
     - 5 * yVar^3 * zVar^6
     + 8 * yVar^3 * zVar^5
     + 8 * yVar^3 * zVar^4
     - 4 * yVar^3 * zVar^3
     - 4 * yVar^3 * zVar^2
     - 2 * yVar^2 * zVar^10
     - 2 * yVar^2 * zVar^9
     + 8 * yVar^2 * zVar^8
     + 6 * yVar^2 * zVar^7
     - 6 * yVar^2 * zVar^6
     + 4 * yVar^2 * zVar^5
     - 8 * yVar^2 * zVar^4
     - 24 * yVar^2 * zVar^3
     + 8 * yVar^2 * zVar^2
     + 16 * yVar^2 * zVar
     - 2 * yVar * zVar^10
     - yVar * zVar^9
     + 15 * yVar * zVar^8
     + 5 * yVar * zVar^7
     - 41 * yVar * zVar^6
     - 8 * yVar * zVar^5
     + 48 * yVar * zVar^4
     + 4 * yVar * zVar^3
     - 20 * yVar * zVar^2
     + 2 * zVar^9
     + 4 * zVar^8
     - 10 * zVar^7
     - 20 * zVar^6
     + 16 * zVar^5
     + 32 * zVar^4
     - 8 * zVar^3
     - 16 * zVar^2

def p3Poly : Poly :=
    4 * xVar^6 * zVar^5 * gVar
     - 16 * xVar^6 * zVar^5
     + 4 * xVar^6 * zVar^4 * gVar
     - 16 * xVar^6 * zVar^4
     + 4 * xVar^5 * yVar * zVar^5 * gVar
     - 16 * xVar^5 * yVar * zVar^5
     + 4 * xVar^5 * yVar * zVar^4 * gVar
     - 16 * xVar^5 * yVar * zVar^4
     + 12 * xVar^5 * zVar^6 * gVar
     - 48 * xVar^5 * zVar^6
     + 20 * xVar^5 * zVar^5 * gVar
     - 80 * xVar^5 * zVar^5
     - 16 * xVar^5 * zVar^4 * gVar
     + 64 * xVar^5 * zVar^4
     - 24 * xVar^5 * zVar^3 * gVar
     + 96 * xVar^5 * zVar^3
     + 12 * xVar^4 * yVar * zVar^6 * gVar
     - 52 * xVar^4 * yVar * zVar^6
     + 16 * xVar^4 * yVar * zVar^5 * gVar
     - 64 * xVar^4 * yVar * zVar^5
     - 16 * xVar^4 * yVar * zVar^4 * gVar
     + 68 * xVar^4 * yVar * zVar^4
     - 20 * xVar^4 * yVar * zVar^3 * gVar
     + 80 * xVar^4 * yVar * zVar^3
     + 13 * xVar^4 * zVar^7 * gVar
     - 52 * xVar^4 * zVar^7
     + 35 * xVar^4 * zVar^6 * gVar
     - 144 * xVar^4 * zVar^6
     - 25 * xVar^4 * zVar^5 * gVar
     + 100 * xVar^4 * zVar^5
     - 95 * xVar^4 * zVar^4 * gVar
     + 384 * xVar^4 * zVar^4
     + 4 * xVar^4 * zVar^3 * gVar
     - 16 * xVar^4 * zVar^3
     + 52 * xVar^4 * zVar^2 * gVar
     - 208 * xVar^4 * zVar^2
     - 4 * xVar^3 * yVar^2 * zVar^6
     + 4 * xVar^3 * yVar^2 * zVar^4
     + 13 * xVar^3 * yVar * zVar^7 * gVar
     - 62 * xVar^3 * yVar * zVar^7
     + 23 * xVar^3 * yVar * zVar^6 * gVar
     - 102 * xVar^3 * yVar * zVar^6
     - 31 * xVar^3 * yVar * zVar^5 * gVar
     + 154 * xVar^3 * yVar * zVar^5
     - 63 * xVar^3 * yVar * zVar^4 * gVar
     + 262 * xVar^3 * yVar * zVar^4
     + 10 * xVar^3 * yVar * zVar^3 * gVar
     - 60 * xVar^3 * yVar * zVar^3
     + 32 * xVar^3 * yVar * zVar^2 * gVar
     - 128 * xVar^3 * yVar * zVar^2
     + 6 * xVar^3 * zVar^8 * gVar
     - 24 * xVar^3 * zVar^8
     + 27 * xVar^3 * zVar^7 * gVar
     - 118 * xVar^3 * zVar^7
     - 3 * xVar^3 * zVar^6 * gVar
     + 6 * xVar^3 * zVar^6
     - 117 * xVar^3 * zVar^5 * gVar
     + 498 * xVar^3 * zVar^5
     - 51 * xVar^3 * zVar^4 * gVar
     + 210 * xVar^3 * zVar^4
     + 146 * xVar^3 * zVar^3 * gVar
     - 604 * xVar^3 * zVar^3
     + 56 * xVar^3 * zVar^2 * gVar
     - 224 * xVar^3 * zVar^2
     - 48 * xVar^3 * zVar * gVar
     + 192 * xVar^3 * zVar
     - 10 * xVar^2 * yVar^2 * zVar^7
     - 2 * xVar^2 * yVar^2 * zVar^6
     + 26 * xVar^2 * yVar^2 * zVar^5
     + 2 * xVar^2 * yVar^2 * zVar^4
     - 16 * xVar^2 * yVar^2 * zVar^3
     + 6 * xVar^2 * yVar * zVar^8 * gVar
     - 32 * xVar^2 * yVar * zVar^8
     + 14 * xVar^2 * yVar * zVar^7 * gVar
     - 80 * xVar^2 * yVar * zVar^7
     - 18 * xVar^2 * yVar * zVar^6 * gVar
     + 108 * xVar^2 * yVar * zVar^6
     - 64 * xVar^2 * yVar * zVar^5 * gVar
     + 324 * xVar^2 * yVar * zVar^5
     - 4 * xVar^2 * yVar * zVar^4 * gVar
     - 44 * xVar^2 * yVar * zVar^4
     + 74 * xVar^2 * yVar * zVar^3 * gVar
     - 340 * xVar^2 * yVar * zVar^3
     + 24 * xVar^2 * yVar * zVar^2 * gVar
     - 64 * xVar^2 * yVar * zVar^2
     - 16 * xVar^2 * yVar * zVar * gVar
     + 64 * xVar^2 * yVar * zVar
     + xVar^2 * zVar^9 * gVar
     - 4 * xVar^2 * zVar^9
     + 9 * xVar^2 * zVar^8 * gVar
     - 44 * xVar^2 * zVar^8
     + 9 * xVar^2 * zVar^7 * gVar
     - 50 * xVar^2 * zVar^7
     - 53 * xVar^2 * zVar^6 * gVar
     + 250 * xVar^2 * zVar^6
     - 80 * xVar^2 * zVar^5 * gVar
     + 362 * xVar^2 * zVar^5
     + 96 * xVar^2 * zVar^4 * gVar
     - 446 * xVar^2 * zVar^4
     + 154 * xVar^2 * zVar^3 * gVar
     - 644 * xVar^2 * zVar^3
     - 64 * xVar^2 * zVar^2 * gVar
     + 288 * xVar^2 * zVar^2
     - 80 * xVar^2 * zVar * gVar
     + 320 * xVar^2 * zVar
     + 16 * xVar^2 * gVar
     - 64 * xVar^2
     - 8 * xVar * yVar^2 * zVar^8
     - 4 * xVar * yVar^2 * zVar^7
     + 32 * xVar * yVar^2 * zVar^6
     + 12 * xVar * yVar^2 * zVar^5
     - 40 * xVar * yVar^2 * zVar^4
     - 8 * xVar * yVar^2 * zVar^3
     + 16 * xVar * yVar^2 * zVar^2
     + xVar * yVar * zVar^9 * gVar
     - 6 * xVar * yVar * zVar^9
     + 3 * xVar * yVar * zVar^8 * gVar
     - 30 * xVar * yVar * zVar^8
     - 3 * xVar * yVar * zVar^7 * gVar
     + 18 * xVar * yVar * zVar^7
     - 23 * xVar * yVar * zVar^6 * gVar
     + 174 * xVar * yVar * zVar^6
     - 14 * xVar * yVar * zVar^5 * gVar
     + 44 * xVar * yVar * zVar^5
     + 44 * xVar * yVar * zVar^4 * gVar
     - 296 * xVar * yVar * zVar^4
     + 44 * xVar * yVar * zVar^3 * gVar
     - 152 * xVar * yVar * zVar^3
     - 20 * xVar * yVar * zVar^2 * gVar
     + 136 * xVar * yVar * zVar^2
     - 24 * xVar * yVar * zVar * gVar
     + 80 * xVar * yVar * zVar
     + xVar * zVar^9 * gVar
     - 6 * xVar * zVar^9
     + 3 * xVar * zVar^8 * gVar
     - 22 * xVar * zVar^8
     - 7 * xVar * zVar^7 * gVar
     + 38 * xVar * zVar^7
     - 31 * xVar * zVar^6 * gVar
     + 174 * xVar * zVar^6
     + 6 * xVar * zVar^5 * gVar
     - 48 * xVar * zVar^5
     + 92 * xVar * zVar^4 * gVar
     - 448 * xVar * zVar^4
     + 20 * xVar * zVar^3 * gVar
     - 48 * xVar * zVar^3
     - 100 * xVar * zVar^2 * gVar
     + 440 * xVar * zVar^2
     - 24 * xVar * zVar * gVar
     + 80 * xVar * zVar
     + 32 * xVar * gVar
     - 128 * xVar
     - 2 * yVar^2 * zVar^9
     - 2 * yVar^2 * zVar^8
     + 10 * yVar^2 * zVar^7
     + 10 * yVar^2 * zVar^6
     - 16 * yVar^2 * zVar^5
     - 16 * yVar^2 * zVar^4
     + 8 * yVar^2 * zVar^3
     + 8 * yVar^2 * zVar^2
     - 4 * yVar * zVar^9
     - 4 * yVar * zVar^8
     - 2 * yVar * zVar^7 * gVar
     + 32 * yVar * zVar^7
     - 4 * yVar * zVar^6 * gVar
     + 36 * yVar * zVar^6
     + 6 * yVar * zVar^5 * gVar
     - 76 * yVar * zVar^5
     + 16 * yVar * zVar^4 * gVar
     - 96 * yVar * zVar^4
     + 48 * yVar * zVar^3
     - 16 * yVar * zVar^2 * gVar
     + 80 * yVar * zVar^2
     - 8 * yVar * zVar * gVar
     + 16 * yVar * zVar
     - 2 * zVar^9
     - 2 * zVar^8
     - 2 * zVar^7 * gVar
     + 22 * zVar^7
     - 4 * zVar^6 * gVar
     + 26 * zVar^6
     + 10 * zVar^5 * gVar
     - 76 * zVar^5
     + 20 * zVar^4 * gVar
     - 96 * zVar^4
     - 16 * zVar^3 * gVar
     + 104 * zVar^3
     - 32 * zVar^2 * gVar
     + 136 * zVar^2
     + 8 * zVar * gVar
     - 48 * zVar
     + 16 * gVar
     - 64

def n1Poly : Poly :=
    4 * xVar^5 * yVar^2 * zVar^3
     + 4 * xVar^5 * yVar * zVar^4
     - 4 * xVar^5 * yVar * zVar^3
     - 8 * xVar^5 * yVar * zVar^2
     - 4 * xVar^5 * zVar^4
     + 12 * xVar^4 * yVar^2 * zVar^4
     + 4 * xVar^4 * yVar^2 * zVar^3
     - 16 * xVar^4 * yVar^2 * zVar^2
     + 8 * xVar^4 * yVar * zVar^5
     - 32 * xVar^4 * yVar * zVar^3
     - 8 * xVar^4 * yVar * zVar^2
     + 16 * xVar^4 * yVar * zVar
     - 4 * xVar^4 * zVar^5
     - 12 * xVar^4 * zVar^4
     + 8 * xVar^4 * zVar^3
     + 13 * xVar^3 * yVar^2 * zVar^5
     + 10 * xVar^3 * yVar^2 * zVar^4
     - 27 * xVar^3 * yVar^2 * zVar^3
     - 24 * xVar^3 * yVar^2 * zVar^2
     + 12 * xVar^3 * yVar^2 * zVar
     + 5 * xVar^3 * yVar * zVar^6
     + 9 * xVar^3 * yVar * zVar^5
     - 31 * xVar^3 * yVar * zVar^4
     - 37 * xVar^3 * yVar * zVar^3
     + 34 * xVar^3 * yVar * zVar^2
     + 28 * xVar^3 * yVar * zVar
     - 8 * xVar^3 * yVar
     - xVar^3 * zVar^6
     - 10 * xVar^3 * zVar^5
     - 9 * xVar^3 * zVar^4
     + 24 * xVar^3 * zVar^3
     - 4 * xVar^3 * zVar^2
     + 2 * xVar^2 * yVar^3 * zVar^3
     - 2 * xVar^2 * yVar^3 * zVar^2
     + 6 * xVar^2 * yVar^2 * zVar^6
     + 8 * xVar^2 * yVar^2 * zVar^5
     - 14 * xVar^2 * yVar^2 * zVar^4
     - 30 * xVar^2 * yVar^2 * zVar^3
     - 6 * xVar^2 * yVar^2 * zVar^2
     + 28 * xVar^2 * yVar^2 * zVar
     + xVar^2 * yVar * zVar^7
     + 6 * xVar^2 * yVar * zVar^6
     - 6 * xVar^2 * yVar * zVar^5
     - 36 * xVar^2 * yVar * zVar^4
     + 7 * xVar^2 * yVar * zVar^3
     + 52 * xVar^2 * yVar * zVar^2
     + 8 * xVar^2 * yVar * zVar
     - 16 * xVar^2 * yVar
     - 2 * xVar^2 * zVar^6
     - 8 * xVar^2 * zVar^5
     + 4 * xVar^2 * zVar^4
     + 26 * xVar^2 * zVar^3
     - 12 * xVar^2 * zVar^2
     + 3 * xVar * yVar^3 * zVar^4
     - 2 * xVar * yVar^3 * zVar^3
     - 5 * xVar * yVar^3 * zVar^2
     + 4 * xVar * yVar^3 * zVar
     + xVar * yVar^2 * zVar^7
     + 2 * xVar * yVar^2 * zVar^6
     - 2 * xVar * yVar^2 * zVar^5
     - 9 * xVar * yVar^2 * zVar^4
     - 13 * xVar * yVar^2 * zVar^3
     + 9 * xVar * yVar^2 * zVar^2
     + 28 * xVar * yVar^2 * zVar
     - 4 * xVar * yVar^2
     + xVar * yVar * zVar^7
     + xVar * yVar * zVar^6
     - 8 * xVar * yVar * zVar^5
     - 9 * xVar * yVar * zVar^4
     + 21 * xVar * yVar * zVar^3
     + 22 * xVar * yVar * zVar^2
     - 8 * xVar * yVar * zVar
     - 12 * xVar * yVar
     - xVar * zVar^6
     - 2 * xVar * zVar^5
     + 7 * xVar * zVar^4
     + 12 * xVar * zVar^3
     - 12 * xVar * zVar^2
     + yVar^3 * zVar^5
     - 3 * yVar^3 * zVar^3
     + 2 * yVar^3 * zVar
     - 2 * yVar^2 * zVar^4
     - 4 * yVar^2 * zVar^3
     + 8 * yVar^2 * zVar^2
     + 10 * yVar^2 * zVar
     - 4 * yVar^2
     - yVar * zVar^5
     + 5 * yVar * zVar^3
     + 4 * yVar * zVar^2
     - 4 * yVar * zVar
     - 4 * yVar
     + 2 * zVar^4
     + 2 * zVar^3
     - 4 * zVar^2

def n2Poly : Poly :=
    4 * xVar^5 * yVar^2 * zVar^2
     + 4 * xVar^5 * yVar * zVar^3
     - 4 * xVar^5 * yVar * zVar^2
     - 4 * xVar^5 * zVar^3
     + 12 * xVar^4 * yVar^2 * zVar^3
     + 4 * xVar^4 * yVar^2 * zVar^2
     - 8 * xVar^4 * yVar^2 * zVar
     + 8 * xVar^4 * yVar * zVar^4
     - 16 * xVar^4 * yVar * zVar^2
     + 8 * xVar^4 * yVar * zVar
     - 4 * xVar^4 * zVar^4
     - 12 * xVar^4 * zVar^3
     + 8 * xVar^4 * zVar^2
     + 13 * xVar^3 * yVar^2 * zVar^4
     + 10 * xVar^3 * yVar^2 * zVar^3
     - 11 * xVar^3 * yVar^2 * zVar^2
     - 16 * xVar^3 * yVar^2 * zVar
     + 4 * xVar^3 * yVar^2
     + 5 * xVar^3 * yVar * zVar^5
     + 9 * xVar^3 * yVar * zVar^4
     - 21 * xVar^3 * yVar * zVar^3
     - 9 * xVar^3 * yVar * zVar^2
     + 20 * xVar^3 * yVar * zVar
     - 4 * xVar^3 * yVar
     - xVar^3 * zVar^5
     - 10 * xVar^3 * zVar^4
     - 9 * xVar^3 * zVar^3
     + 24 * xVar^3 * zVar^2
     - 4 * xVar^3 * zVar
     + 2 * xVar^2 * yVar^3 * zVar^2
     - 2 * xVar^2 * yVar^3 * zVar
     + 6 * xVar^2 * yVar^2 * zVar^5
     + 8 * xVar^2 * yVar^2 * zVar^4
     - 6 * xVar^2 * yVar^2 * zVar^3
     - 14 * xVar^2 * yVar^2 * zVar^2
     - 14 * xVar^2 * yVar^2 * zVar
     + 12 * xVar^2 * yVar^2
     + xVar^2 * yVar * zVar^6
     + 6 * xVar^2 * yVar * zVar^5
     - 4 * xVar^2 * yVar * zVar^4
     - 24 * xVar^2 * yVar * zVar^3
     + 17 * xVar^2 * yVar * zVar^2
     + 12 * xVar^2 * yVar * zVar
     - 8 * xVar^2 * yVar
     - 2 * xVar^2 * zVar^5
     - 8 * xVar^2 * zVar^4
     + 4 * xVar^2 * zVar^3
     + 26 * xVar^2 * zVar^2
     - 12 * xVar^2 * zVar
     + xVar * yVar^3 * zVar^3
     + 2 * xVar * yVar^3 * zVar^2
     - 3 * xVar * yVar^3 * zVar
     + xVar * yVar^2 * zVar^6
     + 2 * xVar * yVar^2 * zVar^5
     - xVar * yVar^2 * zVar^4
     - 8 * xVar * yVar^2 * zVar^3
     - 2 * xVar * yVar^2 * zVar^2
     - 8 * xVar * yVar^2 * zVar
     + 12 * xVar * yVar^2
     + xVar * yVar * zVar^6
     + xVar * yVar * zVar^5
     - 7 * xVar * yVar * zVar^4
     - 6 * xVar * yVar * zVar^3
     + 20 * xVar * yVar * zVar^2
     - 5 * xVar * yVar * zVar
     - 4 * xVar * yVar
     - xVar * zVar^5
     - 2 * xVar * zVar^4
     + 7 * xVar * zVar^3
     + 12 * xVar * zVar^2
     - 12 * xVar * zVar
     + yVar^3 * zVar^3
     - yVar^3 * zVar
     - 2 * yVar^2 * zVar^4
     - 2 * yVar^2 * zVar
     + 4 * yVar^2
     - 2 * yVar * zVar^4
     + yVar * zVar^3
     + 6 * yVar * zVar^2
     - 5 * yVar * zVar
     + 2 * zVar^3
     + 2 * zVar^2
     - 4 * zVar

def cancelF : Poly := xVar*zVar + zVar^2 - 2
def cancelD : Poly := 2*xVar^2*zVar + xVar*zVar^2 + xVar*zVar - 2*xVar - 2
def cancelR : Poly := cancelD + zVar*(2*xVar+zVar+1)*(yVar+1)
def yDen : Poly := 2*zVar*(zVar-1)
def n3Poly : Poly := (gVar-4)*cancelD - yDen*(yVar+1)
def factor1 : Poly := (zVar+1)*zVar*cancelF
def factor2 : Poly := (zVar+1)*zVar*cancelF^2
def factor3 : Poly := (zVar+1)*cancelF^2*cancelR

theorem p1_factor : p1Poly = factor1*n1Poly := by
  simp only [p1Poly, factor1, n1Poly, cancelF]
  ring

theorem p2_factor : p2Poly = factor2*n2Poly := by
  simp only [p2Poly, factor2, n2Poly, cancelF]
  ring

theorem p3_factor : p3Poly = factor3*n3Poly := by
  simp only [p3Poly, factor3, n3Poly, cancelF, cancelR, cancelD, yDen]
  ring

def P1 (x y z g : ℝ) : ℝ := ev (point x y z g) p1Poly
def P2 (x y z g : ℝ) : ℝ := ev (point x y z g) p2Poly
def P3 (x y z g : ℝ) : ℝ := ev (point x y z g) p3Poly
/-- No 4 by 4 determinant, and no replacement by the reduced system. -/
def J (x y z g : ℝ) : ℝ :=
  ev (point x y z g) (jacobianPoly p1Poly p2Poly p3Poly)

end Rho5.Algebraic
