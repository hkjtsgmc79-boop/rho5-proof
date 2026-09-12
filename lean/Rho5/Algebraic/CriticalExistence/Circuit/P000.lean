import Rho5.Algebraic.CriticalExistence.Expression

namespace Rho5.Algebraic.CriticalExistence
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 262144

def e00000 : Expr := .rat (4 : ℚ)

def e00001 : Expr := .var 0

def e00002 : Expr := .rat (1 : ℚ)

def e00003 : Expr := .mul e00002 e00001

def e00004 : Expr := .mul e00003 e00001

def e00005 : Expr := .mul e00004 e00001

def e00006 : Expr := .mul e00005 e00001

def e00007 : Expr := .mul e00006 e00001

def e00008 : Expr := .mul e00007 e00001

def e00009 : Expr := .mul e00000 e00008

def e00010 : Expr := .var 1

def e00011 : Expr := .mul e00002 e00010

def e00012 : Expr := .mul e00011 e00010

def e00013 : Expr := .mul e00009 e00012

def e00014 : Expr := .var 2

def e00015 : Expr := .mul e00002 e00014

def e00016 : Expr := .mul e00015 e00014

def e00017 : Expr := .mul e00016 e00014

def e00018 : Expr := .mul e00017 e00014

def e00019 : Expr := .mul e00018 e00014

def e00020 : Expr := .mul e00019 e00014

def e00021 : Expr := .mul e00013 e00020

def e00022 : Expr := .mul e00013 e00019

def e00023 : Expr := .add e00021 e00022

def e00024 : Expr := .mul e00009 e00010

def e00025 : Expr := .mul e00020 e00014

def e00026 : Expr := .mul e00024 e00025

def e00027 : Expr := .add e00023 e00026

def e00028 : Expr := .rat (12 : ℚ)

def e00029 : Expr := .mul e00028 e00008

def e00030 : Expr := .mul e00029 e00010

def e00031 : Expr := .mul e00030 e00019

def e00032 : Expr := .neg e00031

def e00033 : Expr := .add e00027 e00032

def e00034 : Expr := .rat (8 : ℚ)

def e00035 : Expr := .mul e00034 e00008

def e00036 : Expr := .mul e00035 e00010

def e00037 : Expr := .mul e00036 e00018

def e00038 : Expr := .neg e00037

def e00039 : Expr := .add e00033 e00038

def e00040 : Expr := .mul e00009 e00025

def e00041 : Expr := .neg e00040

def e00042 : Expr := .add e00039 e00041

def e00043 : Expr := .mul e00009 e00020

def e00044 : Expr := .neg e00043

def e00045 : Expr := .add e00042 e00044

def e00046 : Expr := .rat (16 : ℚ)

def e00047 : Expr := .mul e00046 e00007

def e00048 : Expr := .mul e00047 e00012

def e00049 : Expr := .mul e00048 e00025

def e00050 : Expr := .add e00045 e00049

def e00051 : Expr := .rat (20 : ℚ)

def e00052 : Expr := .mul e00051 e00007

def e00053 : Expr := .mul e00052 e00012

def e00054 : Expr := .mul e00053 e00020

def e00055 : Expr := .add e00050 e00054

def e00056 : Expr := .mul e00053 e00019

def e00057 : Expr := .neg e00056

def e00058 : Expr := .add e00055 e00057

def e00059 : Expr := .rat (24 : ℚ)

def e00060 : Expr := .mul e00059 e00007

def e00061 : Expr := .mul e00060 e00012

def e00062 : Expr := .mul e00061 e00018

def e00063 : Expr := .neg e00062

def e00064 : Expr := .add e00058 e00063

def e00065 : Expr := .mul e00028 e00007

def e00066 : Expr := .mul e00065 e00010

def e00067 : Expr := .mul e00025 e00014

def e00068 : Expr := .mul e00066 e00067

def e00069 : Expr := .add e00064 e00068

def e00070 : Expr := .mul e00034 e00007

def e00071 : Expr := .mul e00070 e00010

def e00072 : Expr := .mul e00071 e00025

def e00073 : Expr := .add e00069 e00072

def e00074 : Expr := .rat (52 : ℚ)

def e00075 : Expr := .mul e00074 e00007

def e00076 : Expr := .mul e00075 e00010

def e00077 : Expr := .mul e00076 e00020

def e00078 : Expr := .neg e00077

def e00079 : Expr := .add e00073 e00078

def e00080 : Expr := .rat (48 : ℚ)

def e00081 : Expr := .mul e00080 e00007

def e00082 : Expr := .mul e00081 e00010

def e00083 : Expr := .mul e00082 e00019

def e00084 : Expr := .neg e00083

def e00085 : Expr := .add e00079 e00084

def e00086 : Expr := .rat (32 : ℚ)

def e00087 : Expr := .mul e00086 e00007

def e00088 : Expr := .mul e00087 e00010

def e00089 : Expr := .mul e00088 e00018

def e00090 : Expr := .add e00085 e00089

def e00091 : Expr := .mul e00088 e00017

def e00092 : Expr := .add e00090 e00091

def e00093 : Expr := .mul e00070 e00067

def e00094 : Expr := .neg e00093

def e00095 : Expr := .add e00092 e00094

def e00096 : Expr := .mul e00052 e00025

def e00097 : Expr := .neg e00096

def e00098 : Expr := .add e00095 e00097

def e00099 : Expr := .mul e00000 e00007

def e00100 : Expr := .mul e00099 e00020

def e00101 : Expr := .add e00098 e00100

def e00102 : Expr := .mul e00047 e00019

def e00103 : Expr := .add e00101 e00102

def e00104 : Expr := .rat (25 : ℚ)

def e00105 : Expr := .mul e00104 e00006

def e00106 : Expr := .mul e00105 e00012

def e00107 : Expr := .mul e00106 e00067

def e00108 : Expr := .add e00103 e00107

def e00109 : Expr := .rat (39 : ℚ)

def e00110 : Expr := .mul e00109 e00006

def e00111 : Expr := .mul e00110 e00012

def e00112 : Expr := .mul e00111 e00025

def e00113 : Expr := .add e00108 e00112

def e00114 : Expr := .rat (53 : ℚ)

def e00115 : Expr := .mul e00114 e00006

def e00116 : Expr := .mul e00115 e00012

def e00117 : Expr := .mul e00116 e00020

def e00118 : Expr := .neg e00117

def e00119 : Expr := .add e00113 e00118

def e00120 : Expr := .rat (99 : ℚ)

def e00121 : Expr := .mul e00120 e00006

def e00122 : Expr := .mul e00121 e00012

def e00123 : Expr := .mul e00122 e00019

def e00124 : Expr := .neg e00123

def e00125 : Expr := .add e00119 e00124

def e00126 : Expr := .mul e00028 e00006

def e00127 : Expr := .mul e00126 e00012

def e00128 : Expr := .mul e00127 e00018

def e00129 : Expr := .add e00125 e00128

def e00130 : Expr := .rat (44 : ℚ)

def e00131 : Expr := .mul e00130 e00006

def e00132 : Expr := .mul e00131 e00012

def e00133 : Expr := .mul e00132 e00017

def e00134 : Expr := .add e00129 e00133

def e00135 : Expr := .rat (13 : ℚ)

def e00136 : Expr := .mul e00135 e00006

def e00137 : Expr := .mul e00136 e00010

def e00138 : Expr := .mul e00067 e00014

def e00139 : Expr := .mul e00137 e00138

def e00140 : Expr := .add e00134 e00139

def e00141 : Expr := .rat (22 : ℚ)

def e00142 : Expr := .mul e00141 e00006

def e00143 : Expr := .mul e00142 e00010

def e00144 : Expr := .mul e00143 e00067

def e00145 : Expr := .add e00140 e00144

def e00146 : Expr := .rat (70 : ℚ)

def e00147 : Expr := .mul e00146 e00006

def e00148 : Expr := .mul e00147 e00010

def e00149 : Expr := .mul e00148 e00025

def e00150 : Expr := .neg e00149

def e00151 : Expr := .add e00145 e00150

def e00152 : Expr := .rat (124 : ℚ)

def e00153 : Expr := .mul e00152 e00006

def e00154 : Expr := .mul e00153 e00010

def e00155 : Expr := .mul e00154 e00020

def e00156 : Expr := .neg e00155

def e00157 : Expr := .add e00151 e00156

def e00158 : Expr := .rat (69 : ℚ)

def e00159 : Expr := .mul e00158 e00006

def e00160 : Expr := .mul e00159 e00010

def e00161 : Expr := .mul e00160 e00019

def e00162 : Expr := .add e00157 e00161

def e00163 : Expr := .rat (158 : ℚ)

def e00164 : Expr := .mul e00163 e00006

def e00165 : Expr := .mul e00164 e00010

def e00166 : Expr := .mul e00165 e00018

def e00167 : Expr := .add e00162 e00166

def e00168 : Expr := .mul e00000 e00006

def e00169 : Expr := .mul e00168 e00010

def e00170 : Expr := .mul e00169 e00017

def e00171 : Expr := .add e00167 e00170

def e00172 : Expr := .rat (40 : ℚ)

def e00173 : Expr := .mul e00172 e00006

def e00174 : Expr := .mul e00173 e00010

def e00175 : Expr := .mul e00174 e00016

def e00176 : Expr := .neg e00175

def e00177 : Expr := .add e00171 e00176

def e00178 : Expr := .rat (5 : ℚ)

def e00179 : Expr := .mul e00178 e00006

def e00180 : Expr := .mul e00179 e00138

def e00181 : Expr := .neg e00180

def e00182 : Expr := .add e00177 e00181

def e00183 : Expr := .rat (27 : ℚ)

def e00184 : Expr := .mul e00183 e00006

def e00185 : Expr := .mul e00184 e00067

def e00186 : Expr := .neg e00185

def e00187 : Expr := .add e00182 e00186

def e00188 : Expr := .rat (15 : ℚ)

def e00189 : Expr := .mul e00188 e00006

def e00190 : Expr := .mul e00189 e00025

def e00191 : Expr := .neg e00190

def e00192 : Expr := .add e00187 e00191

def e00193 : Expr := .rat (55 : ℚ)

def e00194 : Expr := .mul e00193 e00006

def e00195 : Expr := .mul e00194 e00020

def e00196 : Expr := .add e00192 e00195

def e00197 : Expr := .rat (28 : ℚ)

def e00198 : Expr := .mul e00197 e00006

def e00199 : Expr := .mul e00198 e00019

def e00200 : Expr := .add e00196 e00199

def e00201 : Expr := .mul e00051 e00006

def e00202 : Expr := .mul e00201 e00018

def e00203 : Expr := .neg e00202

def e00204 : Expr := .add e00200 e00203

def e00205 : Expr := .rat (2 : ℚ)

def e00206 : Expr := .mul e00205 e00005

def e00207 : Expr := .mul e00012 e00010

def e00208 : Expr := .mul e00206 e00207

def e00209 : Expr := .mul e00208 e00020

def e00210 : Expr := .add e00204 e00209

def e00211 : Expr := .mul e00208 e00018

def e00212 : Expr := .neg e00211

def e00213 : Expr := .add e00210 e00212

def e00214 : Expr := .rat (19 : ℚ)

def e00215 : Expr := .mul e00214 e00005

def e00216 : Expr := .mul e00215 e00012

def e00217 : Expr := .mul e00216 e00138

def e00218 : Expr := .add e00213 e00217

def e00219 : Expr := .rat (37 : ℚ)

def e00220 : Expr := .mul e00219 e00005

def e00221 : Expr := .mul e00220 e00012

def e00222 : Expr := .mul e00221 e00067

def e00223 : Expr := .add e00218 e00222

def e00224 : Expr := .rat (49 : ℚ)

def e00225 : Expr := .mul e00224 e00005

def e00226 : Expr := .mul e00225 e00012

def e00227 : Expr := .mul e00226 e00025

def e00228 : Expr := .neg e00227

def e00229 : Expr := .add e00223 e00228

def e00230 : Expr := .rat (141 : ℚ)

def e00231 : Expr := .mul e00230 e00005

def e00232 : Expr := .mul e00231 e00012

def e00233 : Expr := .mul e00232 e00020

def e00234 : Expr := .neg e00233

def e00235 : Expr := .add e00229 e00234

def e00236 : Expr := .rat (14 : ℚ)

def e00237 : Expr := .mul e00236 e00005

def e00238 : Expr := .mul e00237 e00012

def e00239 : Expr := .mul e00238 e00019

def e00240 : Expr := .neg e00239

def e00241 : Expr := .add e00235 e00240

def e00242 : Expr := .rat (136 : ℚ)

def e00243 : Expr := .mul e00242 e00005

def e00244 : Expr := .mul e00243 e00012

def e00245 : Expr := .mul e00244 e00018

def e00246 : Expr := .add e00241 e00245

def e00247 : Expr := .mul e00074 e00005

def e00248 : Expr := .mul e00247 e00012

def e00249 : Expr := .mul e00248 e00017

def e00250 : Expr := .add e00246 e00249

def e00251 : Expr := .mul e00059 e00005

def e00252 : Expr := .mul e00251 e00012

def e00253 : Expr := .mul e00252 e00016

def e00254 : Expr := .neg e00253

def e00255 : Expr := .add e00250 e00254

def e00256 : Expr := .rat (6 : ℚ)

def e00257 : Expr := .mul e00256 e00005

def e00258 : Expr := .mul e00257 e00010

def e00259 : Expr := .mul e00138 e00014

def e00260 : Expr := .mul e00258 e00259

def e00261 : Expr := .add e00255 e00260

def e00262 : Expr := .rat (21 : ℚ)

def e00263 : Expr := .mul e00262 e00005

def e00264 : Expr := .mul e00263 e00010

def e00265 : Expr := .mul e00264 e00138

def e00266 : Expr := .add e00261 e00265

def e00267 : Expr := .mul e00086 e00005

def e00268 : Expr := .mul e00267 e00010

def e00269 : Expr := .mul e00268 e00067

def e00270 : Expr := .neg e00269

def e00271 : Expr := .add e00266 e00270

def e00272 : Expr := .rat (138 : ℚ)

def e00273 : Expr := .mul e00272 e00005

def e00274 : Expr := .mul e00273 e00010

def e00275 : Expr := .mul e00274 e00025

def e00276 : Expr := .neg e00275

def e00277 : Expr := .add e00271 e00276

def e00278 : Expr := .mul e00028 e00005

def e00279 : Expr := .mul e00278 e00010

def e00280 : Expr := .mul e00279 e00020

def e00281 : Expr := .add e00277 e00280

def e00282 : Expr := .rat (257 : ℚ)

def e00283 : Expr := .mul e00282 e00005

def e00284 : Expr := .mul e00283 e00010

def e00285 : Expr := .mul e00284 e00019

def e00286 : Expr := .add e00281 e00285

def e00287 : Expr := .rat (86 : ℚ)

def e00288 : Expr := .mul e00287 e00005

def e00289 : Expr := .mul e00288 e00010

def e00290 : Expr := .mul e00289 e00018

def e00291 : Expr := .add e00286 e00290

def e00292 : Expr := .rat (140 : ℚ)

def e00293 : Expr := .mul e00292 e00005

def e00294 : Expr := .mul e00293 e00010

def e00295 : Expr := .mul e00294 e00017

def e00296 : Expr := .neg e00295

def e00297 : Expr := .add e00291 e00296

def e00298 : Expr := .rat (56 : ℚ)

def e00299 : Expr := .mul e00298 e00005

def e00300 : Expr := .mul e00299 e00010

def e00301 : Expr := .mul e00300 e00016

def e00302 : Expr := .neg e00301

def e00303 : Expr := .add e00297 e00302

def e00304 : Expr := .mul e00046 e00005

def e00305 : Expr := .mul e00304 e00010

def e00306 : Expr := .mul e00305 e00014

def e00307 : Expr := .add e00303 e00306

def e00308 : Expr := .mul e00005 e00259

def e00309 : Expr := .neg e00308

def e00310 : Expr := .add e00307 e00309

def e00311 : Expr := .mul e00135 e00005

def e00312 : Expr := .mul e00311 e00138

def e00313 : Expr := .neg e00312

def e00314 : Expr := .add e00310 e00313

def e00315 : Expr := .mul e00183 e00005

def e00316 : Expr := .mul e00315 e00067

def e00317 : Expr := .neg e00316

def e00318 : Expr := .add e00314 e00317

def e00319 : Expr := .rat (33 : ℚ)

def e00320 : Expr := .mul e00319 e00005

def e00321 : Expr := .mul e00320 e00025

def e00322 : Expr := .add e00318 e00321

def e00323 : Expr := .rat (88 : ℚ)

def e00324 : Expr := .mul e00323 e00005

def e00325 : Expr := .mul e00324 e00020

def e00326 : Expr := .add e00322 e00325

def e00327 : Expr := .mul e00051 e00005

def e00328 : Expr := .mul e00327 e00019

def e00329 : Expr := .neg e00328

def e00330 : Expr := .add e00326 e00329

def e00331 : Expr := .mul e00247 e00018

def e00332 : Expr := .neg e00331

def e00333 : Expr := .add e00330 e00332

def e00334 : Expr := .mul e00034 e00005

def e00335 : Expr := .mul e00334 e00017

def e00336 : Expr := .add e00333 e00335

def e00337 : Expr := .mul e00178 e00004

def e00338 : Expr := .mul e00337 e00207

def e00339 : Expr := .mul e00338 e00025

def e00340 : Expr := .add e00336 e00339

def e00341 : Expr := .mul e00004 e00207

def e00342 : Expr := .mul e00341 e00020

def e00343 : Expr := .add e00340 e00342

def e00344 : Expr := .mul e00135 e00004

def e00345 : Expr := .mul e00344 e00207

def e00346 : Expr := .mul e00345 e00019

def e00347 : Expr := .neg e00346

def e00348 : Expr := .add e00343 e00347

def e00349 : Expr := .mul e00341 e00018

def e00350 : Expr := .neg e00349

def e00351 : Expr := .add e00348 e00350

def e00352 : Expr := .mul e00034 e00004

def e00353 : Expr := .mul e00352 e00207

def e00354 : Expr := .mul e00353 e00017

def e00355 : Expr := .add e00351 e00354

def e00356 : Expr := .rat (7 : ℚ)

def e00357 : Expr := .mul e00356 e00004

def e00358 : Expr := .mul e00357 e00012

def e00359 : Expr := .mul e00358 e00259

def e00360 : Expr := .add e00355 e00359

def e00361 : Expr := .rat (17 : ℚ)

def e00362 : Expr := .mul e00361 e00004

def e00363 : Expr := .mul e00362 e00012

def e00364 : Expr := .mul e00363 e00138

def e00365 : Expr := .add e00360 e00364

def e00366 : Expr := .rat (18 : ℚ)

def e00367 : Expr := .mul e00366 e00004

def e00368 : Expr := .mul e00367 e00012

def e00369 : Expr := .mul e00368 e00067

def e00370 : Expr := .neg e00369

def e00371 : Expr := .add e00365 e00370

def e00372 : Expr := .rat (83 : ℚ)

def e00373 : Expr := .mul e00372 e00004

def e00374 : Expr := .mul e00373 e00012

def e00375 : Expr := .mul e00374 e00025

def e00376 : Expr := .neg e00375

def e00377 : Expr := .add e00371 e00376

def e00378 : Expr := .rat (46 : ℚ)

def e00379 : Expr := .mul e00378 e00004

def e00380 : Expr := .mul e00379 e00012

def e00381 : Expr := .mul e00380 e00020

def e00382 : Expr := .neg e00381

def e00383 : Expr := .add e00377 e00382

def e00384 : Expr := .rat (106 : ℚ)

def e00385 : Expr := .mul e00384 e00004

def e00386 : Expr := .mul e00385 e00012

def e00387 : Expr := .mul e00386 e00019

def e00388 : Expr := .add e00383 e00387

def e00389 : Expr := .rat (137 : ℚ)

def e00390 : Expr := .mul e00389 e00004

def e00391 : Expr := .mul e00390 e00012

def e00392 : Expr := .mul e00391 e00018

def e00393 : Expr := .add e00388 e00392

def e00394 : Expr := .mul e00051 e00004

def e00395 : Expr := .mul e00394 e00012

def e00396 : Expr := .mul e00395 e00017

def e00397 : Expr := .neg e00396

def e00398 : Expr := .add e00393 e00397

def e00399 : Expr := .rat (60 : ℚ)

end
end Rho5.Algebraic.CriticalExistence
