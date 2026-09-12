import Rho5.Algebraic.CandidateSystem

noncomputable section
namespace Rho5.Algebraic

set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Explicit polynomial multipliers. The three relations below are sufficient
for the branch selection and for transporting the critical determinant. -/

def elimX : Poly := 4*xVar*zVar -
  (gVar*zVar^2-gVar*zVar-2*gVar-8*zVar^2+4*zVar+8)
def qY : Poly := -(zVar-2)*(zVar-1)*(zVar+1)
def scale1 : Poly := -yVar*cancelR*(zVar-1)*cancelD
def scale2 : Poly := zVar*(zVar-1)*cancelD^2
def scale3 : Poly := 8*zVar^2
def xDen : Poly := 4*zVar

def smallQ : Poly :=
    4 * xVar^3 * zVar
     + 6 * xVar^2 * zVar^2
     + 2 * xVar^2 * zVar
     - 4 * xVar^2
     + 2 * xVar * zVar^3
     + 2 * xVar * zVar^2
     - 4 * xVar * zVar
     - 4 * xVar
     - yVar * zVar^3
     + 2 * yVar * zVar^2
     + yVar * zVar
     - 2 * yVar
     - zVar^3
     + 2 * zVar^2
     - 3 * zVar
     - 2

def reducedG : Poly :=
    8 * xVar^5 * zVar^2 * gVar^2
     - 64 * xVar^5 * zVar^2 * gVar
     + 128 * xVar^5 * zVar^2
     + 24 * xVar^4 * zVar^3 * gVar^2
     - 192 * xVar^4 * zVar^3 * gVar
     + 384 * xVar^4 * zVar^3
     + 8 * xVar^4 * zVar^2 * gVar^2
     - 64 * xVar^4 * zVar^2 * gVar
     + 128 * xVar^4 * zVar^2
     + 4 * xVar^4 * zVar * gVar^3
     - 64 * xVar^4 * zVar * gVar^2
     + 320 * xVar^4 * zVar * gVar
     - 512 * xVar^4 * zVar
     + 26 * xVar^3 * zVar^4 * gVar^2
     - 200 * xVar^3 * zVar^4 * gVar
     + 384 * xVar^3 * zVar^4
     + 20 * xVar^3 * zVar^3 * gVar^2
     - 192 * xVar^3 * zVar^3 * gVar
     + 448 * xVar^3 * zVar^3
     + 4 * xVar^3 * zVar^2 * gVar^3
     - 70 * xVar^3 * zVar^2 * gVar^2
     + 392 * xVar^3 * zVar^2 * gVar
     - 704 * xVar^3 * zVar^2
     + 8 * xVar^3 * zVar * gVar^3
     - 128 * xVar^3 * zVar * gVar^2
     + 640 * xVar^3 * zVar * gVar
     - 1024 * xVar^3 * zVar
     - 4 * xVar^3 * gVar^3
     + 56 * xVar^3 * gVar^2
     - 256 * xVar^3 * gVar
     + 384 * xVar^3
     + 12 * xVar^2 * zVar^5 * gVar^2
     - 84 * xVar^2 * zVar^5 * gVar
     + 144 * xVar^2 * zVar^5
     + 16 * xVar^2 * zVar^4 * gVar^2
     - 180 * xVar^2 * zVar^4 * gVar
     + 464 * xVar^2 * zVar^4
     + xVar^2 * zVar^3 * gVar^3
     - 24 * xVar^2 * zVar^3 * gVar^2
     + 156 * xVar^2 * zVar^3 * gVar
     - 304 * xVar^2 * zVar^3
     + 6 * xVar^2 * zVar^2 * gVar^3
     - 112 * xVar^2 * zVar^2 * gVar^2
     + 660 * xVar^2 * zVar^2 * gVar
     - 1232 * xVar^2 * zVar^2
     + 3 * xVar^2 * zVar * gVar^3
     - 52 * xVar^2 * zVar * gVar^2
     + 248 * xVar^2 * zVar * gVar
     - 352 * xVar^2 * zVar
     - 10 * xVar^2 * gVar^3
     + 144 * xVar^2 * gVar^2
     - 672 * xVar^2 * gVar
     + 1024 * xVar^2
     + 2 * xVar * zVar^6 * gVar^2
     - 12 * xVar * zVar^6 * gVar
     + 16 * xVar * zVar^6
     + 4 * xVar * zVar^5 * gVar^2
     - 56 * xVar * zVar^5 * gVar
     + 144 * xVar * zVar^5
     - 2 * xVar * zVar^4 * gVar^2
     + 80 * xVar * zVar^4
     + xVar * zVar^3 * gVar^3
     - 34 * xVar * zVar^3 * gVar^2
     + 256 * xVar * zVar^3 * gVar
     - 592 * xVar * zVar^3
     + 2 * xVar * zVar^2 * gVar^3
     - 40 * xVar * zVar^2 * gVar^2
     + 268 * xVar * zVar^2 * gVar
     - 544 * xVar * zVar^2
     - 3 * xVar * zVar * gVar^3
     + 38 * xVar * zVar * gVar^2
     - 200 * xVar * zVar * gVar
     + 384 * xVar * zVar
     - 8 * xVar * gVar^3
     + 120 * xVar * gVar^2
     - 576 * xVar * gVar
     + 896 * xVar
     - 4 * zVar^6 * gVar
     + 8 * zVar^6
     - 4 * zVar^5 * gVar
     + 32 * zVar^5
     - 4 * zVar^4 * gVar^2
     + 28 * zVar^4 * gVar
     - 48 * zVar^4
     - 6 * zVar^3 * gVar^2
     + 68 * zVar^3 * gVar
     - 192 * zVar^3
     + 8 * zVar^2 * gVar
     - 24 * zVar^2
     - 2 * zVar * gVar^3
     + 26 * zVar * gVar^2
     - 128 * zVar * gVar
     + 224 * zVar
     - 2 * gVar^3
     + 32 * gVar^2
     - 160 * gVar
     + 256

def multiplierY : Poly :=
    -16 * xVar^7 * zVar^5 * gVar
     + 64 * xVar^7 * zVar^5
     + 16 * xVar^7 * zVar^4 * gVar
     - 64 * xVar^7 * zVar^4
     - 56 * xVar^6 * zVar^6 * gVar
     + 224 * xVar^6 * zVar^6
     + 32 * xVar^6 * zVar^5 * gVar
     - 128 * xVar^6 * zVar^5
     - 8 * xVar^6 * zVar^4 * gVar^2
     + 136 * xVar^6 * zVar^4 * gVar
     - 416 * xVar^6 * zVar^4
     + 8 * xVar^6 * zVar^3 * gVar^2
     - 112 * xVar^6 * zVar^3 * gVar
     + 320 * xVar^6 * zVar^3
     - 16 * xVar^5 * yVar * zVar^6
     + 32 * xVar^5 * yVar * zVar^5
     - 16 * xVar^5 * yVar * zVar^4
     - 76 * xVar^5 * zVar^7 * gVar
     + 288 * xVar^5 * zVar^7
     + 4 * xVar^5 * zVar^6 * gVar
     + 48 * xVar^5 * zVar^6
     - 12 * xVar^5 * zVar^5 * gVar^2
     + 268 * xVar^5 * zVar^5 * gVar
     - 960 * xVar^5 * zVar^5
     - 8 * xVar^5 * zVar^4 * gVar^2
     + 76 * xVar^5 * zVar^4 * gVar
     - 144 * xVar^5 * zVar^4
     + 36 * xVar^5 * zVar^3 * gVar^2
     - 448 * xVar^5 * zVar^3 * gVar
     + 1216 * xVar^5 * zVar^3
     - 16 * xVar^5 * zVar^2 * gVar^2
     + 176 * xVar^5 * zVar^2 * gVar
     - 448 * xVar^5 * zVar^2
     - 48 * xVar^4 * yVar * zVar^7
     + 80 * xVar^4 * yVar * zVar^6
     - 8 * xVar^4 * yVar * zVar^5 * gVar
     + 48 * xVar^4 * yVar * zVar^5
     + 16 * xVar^4 * yVar * zVar^4 * gVar
     - 144 * xVar^4 * yVar * zVar^4
     - 8 * xVar^4 * yVar * zVar^3 * gVar
     + 64 * xVar^4 * yVar * zVar^3
     - 50 * xVar^4 * zVar^8 * gVar
     + 168 * xVar^4 * zVar^8
     - 28 * xVar^4 * zVar^7 * gVar
     + 224 * xVar^4 * zVar^7
     - 6 * xVar^4 * zVar^6 * gVar^2
     + 204 * xVar^4 * zVar^6 * gVar
     - 768 * xVar^4 * zVar^6
     - 18 * xVar^4 * zVar^5 * gVar^2
     + 280 * xVar^4 * zVar^5 * gVar
     - 1008 * xVar^4 * zVar^5
     + 22 * xVar^4 * zVar^4 * gVar^2
     - 354 * xVar^4 * zVar^4 * gVar
     + 1272 * xVar^4 * zVar^4
     + 50 * xVar^4 * zVar^3 * gVar^2
     - 588 * xVar^4 * zVar^3 * gVar
     + 1488 * xVar^4 * zVar^3
     - 56 * xVar^4 * zVar^2 * gVar^2
     + 616 * xVar^4 * zVar^2 * gVar
     - 1568 * xVar^4 * zVar^2
     + 8 * xVar^4 * zVar * gVar^2
     - 80 * xVar^4 * zVar * gVar
     + 192 * xVar^4 * zVar
     - 52 * xVar^3 * yVar * zVar^8
     + 64 * xVar^3 * yVar * zVar^7
     - 8 * xVar^3 * yVar * zVar^6 * gVar
     + 104 * xVar^3 * yVar * zVar^6
     - 64 * xVar^3 * yVar * zVar^5
     + 32 * xVar^3 * yVar * zVar^4 * gVar
     - 228 * xVar^3 * yVar * zVar^4
     - 32 * xVar^3 * yVar * zVar^3 * gVar
     + 224 * xVar^3 * yVar * zVar^3
     + 8 * xVar^3 * yVar * zVar^2 * gVar
     - 48 * xVar^3 * yVar * zVar^2
     - 16 * xVar^3 * zVar^9 * gVar
     + 44 * xVar^3 * zVar^9
     - 20 * xVar^3 * zVar^8 * gVar
     + 136 * xVar^3 * zVar^8
     - xVar^3 * zVar^7 * gVar^2
     + 68 * xVar^3 * zVar^7 * gVar
     - 184 * xVar^3 * zVar^7
     - 8 * xVar^3 * zVar^6 * gVar^2
     + 212 * xVar^3 * zVar^6 * gVar
     - 960 * xVar^3 * zVar^6
     - 2 * xVar^3 * zVar^5 * gVar^2
     - 60 * xVar^3 * zVar^5 * gVar
     + 268 * xVar^3 * zVar^5
     + 44 * xVar^3 * zVar^4 * gVar^2
     - 560 * xVar^3 * zVar^4 * gVar
     + 1848 * xVar^3 * zVar^4
     + 15 * xVar^3 * zVar^3 * gVar^2
     - 184 * xVar^3 * zVar^3 * gVar
     + 288 * xVar^3 * zVar^3
     - 76 * xVar^3 * zVar^2 * gVar^2
     + 848 * xVar^3 * zVar^2 * gVar
     - 2144 * xVar^3 * zVar^2
     + 28 * xVar^3 * zVar * gVar^2
     - 288 * xVar^3 * zVar * gVar
     + 704 * xVar^3 * zVar
     - 8 * xVar^2 * yVar^2 * zVar^6
     + 24 * xVar^2 * yVar^2 * zVar^5
     - 24 * xVar^2 * yVar^2 * zVar^4
     + 8 * xVar^2 * yVar^2 * zVar^3
     - 24 * xVar^2 * yVar * zVar^9
     + 16 * xVar^2 * yVar * zVar^8
     - 2 * xVar^2 * yVar * zVar^7 * gVar
     + 72 * xVar^2 * yVar * zVar^7
     - 8 * xVar^2 * yVar * zVar^6 * gVar
     + 16 * xVar^2 * yVar * zVar^6
     + 16 * xVar^2 * yVar * zVar^5 * gVar
     - 120 * xVar^2 * yVar * zVar^5
     + 20 * xVar^2 * yVar * zVar^4 * gVar
     - 160 * xVar^2 * yVar * zVar^4
     - 46 * xVar^2 * yVar * zVar^3 * gVar
     + 328 * xVar^2 * yVar * zVar^3
     + 20 * xVar^2 * yVar * zVar^2 * gVar
     - 128 * xVar^2 * yVar * zVar^2
     - 2 * xVar^2 * zVar^10 * gVar
     + 4 * xVar^2 * zVar^10
     - 4 * xVar^2 * zVar^9 * gVar
     + 24 * xVar^2 * zVar^9
     + 8 * xVar^2 * zVar^8 * gVar
     + 12 * xVar^2 * zVar^8
     - xVar^2 * zVar^7 * gVar^2
     + 68 * xVar^2 * zVar^7 * gVar
     - 280 * xVar^2 * zVar^7
     - 2 * xVar^2 * zVar^6 * gVar^2
     + 22 * xVar^2 * zVar^6 * gVar
     - 284 * xVar^2 * zVar^6
     + 8 * xVar^2 * zVar^5 * gVar^2
     - 180 * xVar^2 * zVar^5 * gVar
     + 832 * xVar^2 * zVar^5
     + 26 * xVar^2 * zVar^4 * gVar^2
     - 276 * xVar^2 * zVar^4 * gVar
     + 828 * xVar^2 * zVar^4
     - 19 * xVar^2 * zVar^3 * gVar^2
     + 180 * xVar^2 * zVar^3 * gVar
     - 672 * xVar^2 * zVar^3
     - 48 * xVar^2 * zVar^2 * gVar^2
     + 568 * xVar^2 * zVar^2 * gVar
     - 1424 * xVar^2 * zVar^2
     + 36 * xVar^2 * zVar * gVar^2
     - 384 * xVar^2 * zVar * gVar
     + 960 * xVar^2 * zVar
     - 4 * xVar * yVar^2 * zVar^7
     + 24 * xVar * yVar^2 * zVar^5
     - 32 * xVar * yVar^2 * zVar^4
     + 12 * xVar * yVar^2 * zVar^3
     - 4 * xVar * yVar * zVar^10
     + 16 * xVar * yVar * zVar^8
     - 2 * xVar * yVar * zVar^7 * gVar
     + 28 * xVar * yVar * zVar^7
     - 52 * xVar * yVar * zVar^6
     + 12 * xVar * yVar * zVar^5 * gVar
     - 24 * xVar * yVar * zVar^5
     - 72 * xVar * yVar * zVar^4
     - 26 * xVar * yVar * zVar^3 * gVar
     + 220 * xVar * yVar * zVar^3
     + 16 * xVar * yVar * zVar^2 * gVar
     - 112 * xVar * yVar * zVar^2
     + 4 * xVar * zVar^9
     + 8 * xVar * zVar^8 * gVar
     - 16 * xVar * zVar^8
     + 8 * xVar * zVar^7 * gVar
     - 88 * xVar * zVar^7
     - 24 * xVar * zVar^6 * gVar
     + 48 * xVar * zVar^6
     + 4 * xVar * zVar^5 * gVar^2
     - 72 * xVar * zVar^5 * gVar
     + 404 * xVar * zVar^5
     + 4 * xVar * zVar^4 * gVar^2
     - 16 * xVar * zVar^4 * gVar
     - 32 * xVar * zVar^4
     - 16 * xVar * zVar^3 * gVar^2
     + 144 * xVar * zVar^3 * gVar
     - 448 * xVar * zVar^3
     - 12 * xVar * zVar^2 * gVar^2
     + 176 * xVar * zVar^2 * gVar
     - 448 * xVar * zVar^2
     + 20 * xVar * zVar * gVar^2
     - 224 * xVar * zVar * gVar
     + 576 * xVar * zVar
     - 4 * yVar^2 * zVar^7
     + 8 * yVar^2 * zVar^6
     - 8 * yVar^2 * zVar^4
     + 4 * yVar^2 * zVar^3
     + 8 * yVar * zVar^8
     - 12 * yVar * zVar^7
     + 4 * yVar * zVar^5 * gVar
     - 8 * yVar * zVar^5
     - 4 * yVar * zVar^4 * gVar
     - 8 * yVar * zVar^4
     - 4 * yVar * zVar^3 * gVar
     + 52 * yVar * zVar^3
     + 4 * yVar * zVar^2 * gVar
     - 32 * yVar * zVar^2
     - 8 * zVar^7
     - 8 * zVar^6 * gVar
     + 24 * zVar^6
     + 56 * zVar^5
     + 8 * zVar^4 * gVar
     - 72 * zVar^4
     - 4 * zVar^3 * gVar^2
     + 32 * zVar^3 * gVar
     - 80 * zVar^3
     + 16 * zVar^2 * gVar
     - 48 * zVar^2
     + 4 * zVar * gVar^2
     - 48 * zVar * gVar
     + 128 * zVar

def multiplierX : Poly :=
    2048 * xVar^4 * zVar^6 * gVar^2
     - 16384 * xVar^4 * zVar^6 * gVar
     + 32768 * xVar^4 * zVar^6
     + 512 * xVar^3 * zVar^7 * gVar^3
     - 2048 * xVar^3 * zVar^7 * gVar^2
     - 8192 * xVar^3 * zVar^7 * gVar
     + 32768 * xVar^3 * zVar^7
     - 512 * xVar^3 * zVar^6 * gVar^3
     + 8192 * xVar^3 * zVar^6 * gVar^2
     - 40960 * xVar^3 * zVar^6 * gVar
     + 65536 * xVar^3 * zVar^6
     - 4096 * xVar^3 * zVar^5 * gVar^2
     + 32768 * xVar^3 * zVar^5 * gVar
     - 65536 * xVar^3 * zVar^5
     + 128 * xVar^2 * zVar^8 * gVar^4
     - 1536 * xVar^2 * zVar^8 * gVar^3
     + 8704 * xVar^2 * zVar^8 * gVar^2
     - 26624 * xVar^2 * zVar^8 * gVar
     + 32768 * xVar^2 * zVar^8
     - 256 * xVar^2 * zVar^7 * gVar^4
     + 4096 * xVar^2 * zVar^7 * gVar^3
     - 21504 * xVar^2 * zVar^7 * gVar^2
     + 32768 * xVar^2 * zVar^7 * gVar
     + 16384 * xVar^2 * zVar^7
     - 128 * xVar^2 * zVar^6 * gVar^4
     - 512 * xVar^2 * zVar^6 * gVar^3
     + 16896 * xVar^2 * zVar^6 * gVar^2
     - 71680 * xVar^2 * zVar^6 * gVar
     + 81920 * xVar^2 * zVar^6
     + 256 * xVar^2 * zVar^5 * gVar^4
     - 2048 * xVar^2 * zVar^5 * gVar^3
     - 8192 * xVar^2 * zVar^5 * gVar^2
     + 98304 * xVar^2 * zVar^5 * gVar
     - 196608 * xVar^2 * zVar^5
     + 1024 * xVar^2 * zVar^4 * gVar^3
     - 10240 * xVar^2 * zVar^4 * gVar^2
     + 32768 * xVar^2 * zVar^4 * gVar
     - 32768 * xVar^2 * zVar^4
     + 32 * xVar * zVar^9 * gVar^5
     - 640 * xVar * zVar^9 * gVar^4
     + 5248 * xVar * zVar^9 * gVar^3
     - 20992 * xVar * zVar^9 * gVar^2
     + 39936 * xVar * zVar^9 * gVar
     - 28672 * xVar * zVar^9
     - 96 * xVar * zVar^8 * gVar^5
     + 2048 * xVar * zVar^8 * gVar^4
     - 17280 * xVar * zVar^8 * gVar^3
     + 70656 * xVar * zVar^8 * gVar^2
     - 142336 * xVar * zVar^8 * gVar
     + 118784 * xVar * zVar^8
     - 32 * xVar * zVar^7 * gVar^5
     - 128 * xVar * zVar^7 * gVar^4
     + 7552 * xVar * zVar^7 * gVar^3
     - 56832 * xVar * zVar^7 * gVar^2
     + 162816 * xVar * zVar^7 * gVar
     - 159744 * xVar * zVar^7
     + 224 * xVar * zVar^6 * gVar^5
     - 3584 * xVar * zVar^6 * gVar^4
     + 17792 * xVar * zVar^6 * gVar^3
     - 12288 * xVar * zVar^6 * gVar^2
     - 111616 * xVar * zVar^6 * gVar
     + 192512 * xVar * zVar^6
     + 1024 * xVar * zVar^5 * gVar^4
     - 13312 * xVar * zVar^5 * gVar^3
     + 52224 * xVar * zVar^5 * gVar^2
     - 47104 * xVar * zVar^5 * gVar
     - 57344 * xVar * zVar^5
     - 128 * xVar * zVar^4 * gVar^5
     + 1280 * xVar * zVar^4 * gVar^4
     + 1024 * xVar * zVar^4 * gVar^3
     - 47104 * xVar * zVar^4 * gVar^2
     + 163840 * xVar * zVar^4 * gVar
     - 163840 * xVar * zVar^4
     - 512 * xVar * zVar^3 * gVar^4
     + 7168 * xVar * zVar^3 * gVar^3
     - 36864 * xVar * zVar^3 * gVar^2
     + 81920 * xVar * zVar^3 * gVar
     - 65536 * xVar * zVar^3
     + 8 * zVar^10 * gVar^6
     - 224 * zVar^10 * gVar^5
     + 2592 * zVar^10 * gVar^4
     - 15744 * zVar^10 * gVar^3
     + 52480 * zVar^10 * gVar^2
     - 90112 * zVar^10 * gVar
     + 61440 * zVar^10
     - 32 * zVar^9 * gVar^6
     + 896 * zVar^9 * gVar^5
     - 10368 * zVar^9 * gVar^4
     + 62720 * zVar^9 * gVar^3
     - 206848 * zVar^9 * gVar^2
     + 347136 * zVar^9 * gVar
     - 229376 * zVar^9
     - 192 * zVar^8 * gVar^5
     + 4608 * zVar^8 * gVar^4
     - 43264 * zVar^8 * gVar^3
     + 198144 * zVar^8 * gVar^2
     - 443392 * zVar^8 * gVar
     + 401408 * zVar^8
     + 112 * zVar^7 * gVar^6
     - 2560 * zVar^7 * gVar^5
     + 22336 * zVar^7 * gVar^4
     - 86528 * zVar^7 * gVar^3
     + 102912 * zVar^7 * gVar^2
     + 195584 * zVar^7 * gVar
     - 458752 * zVar^7
     - 40 * zVar^6 * gVar^6
     + 1376 * zVar^6 * gVar^5
     - 17440 * zVar^6 * gVar^4
     + 104576 * zVar^6 * gVar^3
     - 305920 * zVar^6 * gVar^2
     + 394240 * zVar^6 * gVar
     - 151552 * zVar^6
     - 144 * zVar^5 * gVar^6
     + 2560 * zVar^5 * gVar^5
     - 14016 * zVar^5 * gVar^4
     + 768 * zVar^5 * gVar^3
     + 240128 * zVar^5 * gVar^2
     - 772096 * zVar^5 * gVar
     + 753664 * zVar^5
     + 32 * zVar^4 * gVar^6
     - 1088 * zVar^4 * gVar^5
     + 12544 * zVar^4 * gVar^4
     - 65536 * zVar^4 * gVar^3
     + 164864 * zVar^4 * gVar^2
     - 188416 * zVar^4 * gVar
     + 81920 * zVar^4
     + 64 * zVar^3 * gVar^6
     - 768 * zVar^3 * gVar^5
     - 256 * zVar^3 * gVar^4
     + 41984 * zVar^3 * gVar^3
     - 233472 * zVar^3 * gVar^2
     + 507904 * zVar^3 * gVar
     - 393216 * zVar^3
     + 256 * zVar^2 * gVar^5
     - 4608 * zVar^2 * gVar^4
     + 32768 * zVar^2 * gVar^3
     - 114688 * zVar^2 * gVar^2
     + 196608 * zVar^2 * gVar
     - 131072 * zVar^2

def pc0 : Poly :=
    -64 * gVar^6
     + 1408 * gVar^5
     - 12800 * gVar^4
     + 61440 * gVar^3
     - 163840 * gVar^2
     + 229376 * gVar
     - 131072

def pc1 : Poly :=
    -16 * gVar^7
     + 224 * gVar^6
     - 17152 * gVar^4
     + 131072 * gVar^3
     - 442368 * gVar^2
     + 720896 * gVar
     - 458752

def pc2 : Poly :=
    -16 * gVar^7
     + 464 * gVar^6
     - 5408 * gVar^5
     + 32256 * gVar^4
     - 103680 * gVar^3
     + 171008 * gVar^2
     - 118784 * gVar
     + 16384

def pc3 : Poly :=
    40 * gVar^7
     - 792 * gVar^6
     + 4688 * gVar^5
     + 5760 * gVar^4
     - 184064 * gVar^3
     + 840192 * gVar^2
     - 1642496 * gVar
     + 1220608

def pc4 : Poly :=
    32 * gVar^7
     - 944 * gVar^6
     + 11424 * gVar^5
     - 71424 * gVar^4
     + 237312 * gVar^3
     - 372992 * gVar^2
     + 134144 * gVar
     + 172032

def pc5 : Poly :=
    -41 * gVar^7
     + 1024 * gVar^6
     - 9588 * gVar^5
     + 36288 * gVar^4
     + 7520 * gVar^3
     - 484864 * gVar^2
     + 1393664 * gVar
     - 1291264

def pc6 : Poly :=
    -19 * gVar^7
     + 636 * gVar^6
     - 8972 * gVar^5
     + 67920 * gVar^4
     - 291744 * gVar^3
     + 690432 * gVar^2
     - 793088 * gVar
     + 299008

def pc7 : Poly :=
    22 * gVar^7
     - 664 * gVar^6
     + 8168 * gVar^5
     - 51488 * gVar^4
     + 167424 * gVar^3
     - 218112 * gVar^2
     - 116736 * gVar
     + 423936

def pc8 : Poly :=
    2 * gVar^7
     - 88 * gVar^6
     + 1640 * gVar^5
     - 16512 * gVar^4
     + 96384 * gVar^3
     - 325376 * gVar^2
     + 589824 * gVar
     - 450560

def pc9 : Poly :=
    -5 * gVar^7
     + 176 * gVar^6
     - 2628 * gVar^5
     + 21472 * gVar^4
     - 103008 * gVar^3
     + 287744 * gVar^2
     - 429056 * gVar
     + 261120

def pc10 : Poly :=
    gVar^7
     - 36 * gVar^6
     + 548 * gVar^5
     - 4560 * gVar^4
     + 22304 * gVar^3
     - 63744 * gVar^2
     + 97792 * gVar
     - 61440

def elimP : Poly :=
  pc0 + pc1*zVar + pc2*zVar^2 + pc3*zVar^3 + pc4*zVar^4 + pc5*zVar^5 + pc6*zVar^6 + pc7*zVar^7 + pc8*zVar^8 + pc9*zVar^9 + pc10*zVar^10

def elimDP : Poly :=
  1*pc1 + 2*pc2*zVar + 3*pc3*zVar^2 + 4*pc4*zVar^3 + 5*pc5*zVar^4 + 6*pc6*zVar^5 + 7*pc7*zVar^6 + 8*pc8*zVar^7 + 9*pc9*zVar^8 + 10*pc10*zVar^9

theorem smallQ_relation : n1Poly-zVar*n2Poly = -yVar*cancelR*smallQ := by
  simp only [n1Poly, n2Poly, cancelR, cancelD, smallQ]
  ring

theorem first_elimination : scale1*elimX =
    yDen*n1Poly + (-(yDen*zVar))*n2Poly + (-(yVar*cancelR*qY))*n3Poly := by
  simp only [scale1, elimX, yDen, n1Poly, n2Poly, n3Poly, cancelR, cancelD, qY]
  ring

theorem second_elimination : scale2*reducedG =
    (0:Poly)*elimX + yDen^3*n2Poly + (-multiplierY)*n3Poly := by
  simp only [scale2, reducedG, multiplierY, yDen, n2Poly, n3Poly, cancelD]
  ring

theorem third_elimination : scale3*elimP =
    (-multiplierX)*elimX + xDen^5*reducedG + (0:Poly)*n3Poly := by
  simp only [scale3, elimP, multiplierX, elimX, xDen, reducedG]
  simp only [pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10]
  ring

/-- Local numeral-shaped rule: match `OfNat` literals without changing coefficients. -/
private theorem d05_pderiv_ofNat (i : Fin 4) (n : ℕ) [n.AtLeastTwo] :
    MvPolynomial.pderiv i (ofNat(n) : Poly) = 0 :=
  (MvPolynomial.pderiv i).map_natCast n

theorem elimP_deriv_0 : MvPolynomial.pderiv (0:Fin 4) elimP = 0 := by
  simp [d05_pderiv_ofNat, elimP, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, gVar, zVar, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]

theorem elimP_deriv_1 : MvPolynomial.pderiv (1:Fin 4) elimP = 0 := by
  simp [d05_pderiv_ofNat, elimP, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, gVar, zVar, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]

theorem elimP_deriv_z : MvPolynomial.pderiv (2:Fin 4) elimP = elimDP := by
  simp [d05_pderiv_ofNat, elimP, elimDP, pc0, pc1, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9, pc10, gVar, zVar, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;> ring

theorem elimX_deriv_x : MvPolynomial.pderiv (0:Fin 4) elimX = 4*zVar := by
  simp [d05_pderiv_ofNat, elimX, xVar, zVar, gVar, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow] <;> ring

theorem elimX_deriv_y : MvPolynomial.pderiv (1:Fin 4) elimX = 0 := by
  simp [d05_pderiv_ofNat, elimX, xVar, zVar, gVar, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow]

theorem n3_deriv_y : MvPolynomial.pderiv (1:Fin 4) n3Poly = -yDen := by
  simp [d05_pderiv_ofNat, n3Poly, cancelD, yDen, xVar, yVar, zVar, gVar,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;> ring

/-- Rows are (elimX, elimP, n3), columns are x,y,z. -/
theorem triangular_jacobian : jacobianPoly elimX elimP n3Poly =
    (4*zVar*yDen)*elimDP := by
  simp only [jacobianPoly, det3]
  rw [elimX_deriv_x, elimX_deriv_y, elimP_deriv_0, elimP_deriv_1,
    elimP_deriv_z, n3_deriv_y]
  ring

end Rho5.Algebraic
