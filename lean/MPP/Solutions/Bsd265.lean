import Mathlib

namespace MPP.Solutions.Bsd265

theorem dbl_alg {K : Type} [Field K] (a₁ a₂ a₃ a₄ a₆ b₂ b₄ b₆ b₈ x y s t : K)
    (hb2 : b₂ = a₁ ^ 2 + 4 * a₂) (hb4 : b₄ = a₁ * a₃ + 2 * a₄) (hb6 : b₆ = a₃ ^ 2 + 4 * a₆)
    (hb8 : b₈ = a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2)
    (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hs : s * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (ht : t = s ^ 2 + a₁ * s - a₂ - 2 * x) :
    t * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) = x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈ := by
  subst hb2 hb4 hb6 hb8
  linear_combination (-4 * t - (a₁ ^ 2 + 4 * a₂ + 8 * x)) * hE +
    (2 * y + a₁ * x + a₃) ^ 2 * ht +
    (s * (2 * y + a₁ * x + a₃) + (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      a₁ * (2 * y + a₁ * x + a₃)) * hs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ident_b {K : Type} [CommRing K] (b₂ b₄ b₆ b₈ x : K)
    (hR : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    (2 * x ^ 6 + b₂ * x ^ 5 + 5 * b₄ * x ^ 4 + 10 * b₆ * x ^ 3 + 10 * b₈ * x ^ 2 + (b₂ * b₈ - b₄ * b₆) * x + (b₄ * b₈ - b₆ ^ 2)) ^ 2 * (((x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) ^ 4 - b₄ * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) ^ 2 * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 2 - 2 * b₆ * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 3 - b₈ * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 4) - x * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) * (4 * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) ^ 3 + b₂ * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) ^ 2 * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) + 2 * b₄ * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 2 + b₆ * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 3)) + (3 * x ^ 4 + b₂ * x ^ 3 + 3 * b₄ * x ^ 2 + 3 * b₆ * x + b₈) * ((2 * x ^ 6 + b₂ * x ^ 5 + 5 * b₄ * x ^ 4 + 10 * b₆ * x ^ 3 + 10 * b₈ * x ^ 2 + (b₂ * b₈ - b₄ * b₆) * x + (b₄ * b₈ - b₆ ^ 2)) * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 2 - (3 * x ^ 4 + b₂ * x ^ 3 + 3 * b₄ * x ^ 2 + 3 * b₆ * x + b₈) ^ 3) * (4 * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) ^ 3 + b₂ * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) ^ 2 * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) + 2 * b₄ * (x ^ 4 - b₄ * x ^ 2 - 2 * b₆ * x - b₈) * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 2 + b₆ * (4 * x ^ 3 + b₂ * x ^ 2 + 2 * b₄ * x + b₆) ^ 3) = 0 := by
  linear_combination (-b₂^6*b₈*x^14 + b₂^5*b₄*b₆*x^14 - 14*b₂^5*b₄*b₈*x^13 + b₂^5*b₆^2*x^13 - 12*b₂^5*b₆*b₈*x^12 - 3*b₂^5*b₆*x^16 - 4*b₂^5*b₈^2*x^11 - 24*b₂^5*b₈*x^15 + 13*b₂^4*b₄^2*b₆*x^13 - 79*b₂^4*b₄^2*b₈*x^12 + 3*b₂^4*b₄^2*x^16 + 25*b₂^4*b₄*b₆^2*x^12 - 126*b₂^4*b₄*b₆*b₈*x^11 - 10*b₂^4*b₄*b₆*x^15 - 42*b₂^4*b₄*b₈^2*x^10 - 280*b₂^4*b₄*b₈*x^14 - 2*b₂^4*b₄*x^18 + 12*b₂^4*b₆^3*x^11 - 46*b₂^4*b₆^2*b₈*x^10 - 7*b₂^4*b₆^2*x^14 - 30*b₂^4*b₆*b₈^2*x^9 - 250*b₂^4*b₆*b₈*x^13 - 56*b₂^4*b₆*x^17 - 4*b₂^4*b₈^3*x^8 - 81*b₂^4*b₈^2*x^12 - 238*b₂^4*b₈*x^16 - b₂^4*x^20 + 66*b₂^3*b₄^3*b₆*x^12 - 230*b₂^3*b₄^3*b₈*x^11 + 34*b₂^3*b₄^3*x^15 + 184*b₂^3*b₄^2*b₆^2*x^11 - 507*b₂^3*b₄^2*b₆*b₈*x^10 + 151*b₂^3*b₄^2*b₆*x^14 - 171*b₂^3*b₄^2*b₈^2*x^9 - 1238*b₂^3*b₄^2*b₈*x^13 + 21*b₂^3*b₄^2*x^17 + 168*b₂^3*b₄*b₆^3*x^10 - 334*b₂^3*b₄*b₆^2*b₈*x^9 + 266*b₂^3*b₄*b₆^2*x^13 - 230*b₂^3*b₄*b₆*b₈^2*x^8 - 2012*b₂^3*b₄*b₆*b₈*x^12 - 326*b₂^3*b₄*b₆*x^16 - 30*b₂^3*b₄*b₈^3*x^7 - 658*b₂^3*b₄*b₈^2*x^11 - 2242*b₂^3*b₄*b₈*x^15 - 46*b₂^3*b₄*x^19 + 50*b₂^3*b₆^4*x^9 - 62*b₂^3*b₆^3*b₈*x^8 + 156*b₂^3*b₆^3*x^12 - 70*b₂^3*b₆^2*b₈^2*x^7 - 708*b₂^3*b₆^2*b₈*x^11 - 270*b₂^3*b₆^2*x^15 - 17*b₂^3*b₆*b₈^3*x^6 - 445*b₂^3*b₆*b₈^2*x^10 - 2091*b₂^3*b₆*b₈*x^14 - 439*b₂^3*b₆*x^18 - b₂^3*b₈^4*x^5 - 56*b₂^3*b₈^3*x^9 - 662*b₂^3*b₈^2*x^13 - 1256*b₂^3*b₈*x^17 - 9*b₂^3*x^21 + 164*b₂^2*b₄^4*b₆*x^11 - 364*b₂^2*b₄^4*b₈*x^10 + 141*b₂^2*b₄^4*x^14 + 591*b₂^2*b₄^3*b₆^2*x^10 - 970*b₂^2*b₄^3*b₆*b₈*x^9 + 1034*b₂^2*b₄^3*b₆*x^13 - 337*b₂^2*b₄^3*b₈^2*x^8 - 2562*b₂^2*b₄^3*b₈*x^12 + 287*b₂^2*b₄^3*x^16 + 779*b₂^2*b₄^2*b₆^3*x^9 - 831*b₂^2*b₄^2*b₆^2*b₈*x^8 + 2451*b₂^2*b₄^2*b₆^2*x^12 - 636*b₂^2*b₄^2*b₆*b₈^2*x^7 - 5484*b₂^2*b₄^2*b₆*b₈*x^11 + 360*b₂^2*b₄^2*b₆*x^15 - 82*b₂^2*b₄^2*b₈^3*x^6 - 1872*b₂^2*b₄^2*b₈^2*x^10 - 7362*b₂^2*b₄^2*b₈*x^14 - 124*b₂^2*b₄^2*x^18 + 444*b₂^2*b₄*b₆^4*x^8 - 232*b₂^2*b₄*b₆^3*b₈*x^7 + 2360*b₂^2*b₄*b₆^3*x^11 - 357*b₂^2*b₄*b₆^2*b₈^2*x^6 - 3054*b₂^2*b₄*b₆^2*b₈*x^10 + 627*b₂^2*b₄*b₆^2*x^14 - 88*b₂^2*b₄*b₆*b₈^3*x^5 - 2184*b₂^2*b₄*b₆*b₈^2*x^9 - 12288*b₂^2*b₄*b₆*b₈*x^13 - 2592*b₂^2*b₄*b₆*x^17 - 5*b₂^2*b₄*b₈^4*x^4 - 256*b₂^2*b₄*b₈^3*x^8 - 3942*b₂^2*b₄*b₈^2*x^12 - 9088*b₂^2*b₄*b₈*x^16 - 277*b₂^2*b₄*x^20 + 92*b₂^2*b₆^5*x^7 - 3*b₂^2*b₆^4*b₈*x^6 + 788*b₂^2*b₆^4*x^10 - 57*b₂^2*b₆^3*b₈^2*x^5 - 226*b₂^2*b₆^3*b₈*x^9 + 651*b₂^2*b₆^3*x^13 - 21*b₂^2*b₆^2*b₈^3*x^4 - 411*b₂^2*b₆^2*b₈^2*x^8 - 4251*b₂^2*b₆^2*b₈*x^12 - 2125*b₂^2*b₆^2*x^16 - 2*b₂^2*b₆*b₈^4*x^3 - 60*b₂^2*b₆*b₈^3*x^7 - 2568*b₂^2*b₆*b₈^2*x^11 - 8916*b₂^2*b₆*b₈*x^15 - 1702*b₂^2*b₆*x^19 + 5*b₂^2*b₈^4*x^6 - 308*b₂^2*b₈^3*x^10 - 2754*b₂^2*b₈^2*x^14 - 3700*b₂^2*b₈*x^18 - 27*b₂^2*x^22 + 200*b₂*b₄^5*b₆*x^10 - 296*b₂*b₄^5*b₈*x^9 + 254*b₂*b₄^5*x^13 + 876*b₂*b₄^4*b₆^2*x^9 - 868*b₂*b₄^4*b₆*b₈*x^8 + 2283*b₂*b₄^4*b₆*x^12 - 320*b₂*b₄^4*b₈^2*x^7 - 2420*b₂*b₄^4*b₈*x^11 + 912*b₂*b₄^4*x^15 + 1492*b₂*b₄^3*b₆^3*x^8 - 778*b₂*b₄^3*b₆^2*b₈*x^7 + 6714*b₂*b₄^3*b₆^2*x^11 - 742*b₂*b₄^3*b₆*b₈^2*x^6 - 5536*b₂*b₄^3*b₆*b₈*x^10 + 4542*b₂*b₄^3*b₆*x^14 - 96*b₂*b₄^3*b₈^3*x^5 - 2144*b₂*b₄^3*b₈^2*x^9 - 9696*b₂*b₄^3*b₈*x^13 + 400*b₂*b₄^3*x^17 + 1234*b₂*b₄^2*b₆^4*x^7 - 105*b₂*b₄^2*b₆^3*b₈*x^6 + 8869*b₂*b₄^2*b₆^3*x^10 - 555*b₂*b₄^2*b₆^2*b₈^2*x^5 - 2202*b₂*b₄^2*b₆^2*b₈*x^9 + 10185*b₂*b₄^2*b₆^2*x^13 - 144*b₂*b₄^2*b₆*b₈^3*x^4 - 2838*b₂*b₄^2*b₆*b₈^2*x^8 - 20244*b₂*b₄^2*b₆*b₈*x^12 - 2246*b₂*b₄^2*b₆*x^16 - 8*b₂*b₄^2*b₈^4*x^3 - 292*b₂*b₄^2*b₈^3*x^7 - 6972*b₂*b₄^2*b₈^2*x^11 - 20172*b₂*b₄^2*b₈*x^15 - 908*b₂*b₄^2*x^19 + 495*b₂*b₄*b₆^5*x^6 + 152*b₂*b₄*b₆^4*b₈*x^5 + 5418*b₂*b₄*b₆^4*x^9 - 140*b₂*b₄*b₆^3*b₈^2*x^4 + 2112*b₂*b₄*b₆^3*b₈*x^8 + 10548*b₂*b₄*b₆^3*x^12 - 62*b₂*b₄*b₆^2*b₈^3*x^3 + 42*b₂*b₄*b₆^2*b₈^2*x^7 - 9066*b₂*b₄*b₆^2*b₈*x^11 - 3042*b₂*b₄*b₆^2*x^15 - 6*b₂*b₄*b₆*b₈^4*x^2 + 188*b₂*b₄*b₆*b₈^3*x^6 - 6840*b₂*b₄*b₆*b₈^2*x^10 - 35308*b₂*b₄*b₆*b₈*x^14 - 8082*b₂*b₄*b₆*x^18 + 58*b₂*b₄*b₈^4*x^5 - 680*b₂*b₄*b₈^3*x^9 - 10964*b₂*b₄*b₈^2*x^13 - 18504*b₂*b₄*b₈*x^17 - 630*b₂*b₄*x^21 + 77*b₂*b₆^6*x^5 + 50*b₂*b₆^5*b₈*x^4 + 1239*b₂*b₆^5*x^8 - 4*b₂*b₆^4*b₈^2*x^3 + 1224*b₂*b₆^4*b₈*x^7 + 3888*b₂*b₆^4*x^11 - 7*b₂*b₆^3*b₈^3*x^2 + 693*b₂*b₆^3*b₈^2*x^6 + 1027*b₂*b₆^3*b₈*x^10 + 31*b₂*b₆^3*x^14 - b₂*b₆^2*b₈^4*x + 332*b₂*b₆^2*b₈^3*x^5 - 66*b₂*b₆^2*b₈^2*x^9 - 12700*b₂*b₆^2*b₈*x^13 - 6573*b₂*b₆^2*x^17 + 87*b₂*b₆*b₈^4*x^4 + 292*b₂*b₆*b₈^3*x^8 - 7222*b₂*b₆*b₈^2*x^12 - 19164*b₂*b₆*b₈*x^16 - 3177*b₂*b₆*x^20 + 8*b₂*b₈^5*x^3 + 84*b₂*b₈^4*x^7 - 848*b₂*b₈^3*x^11 - 5784*b₂*b₈^2*x^15 - 5720*b₂*b₈*x^19 - 28*b₂*x^23 + 96*b₄^6*b₆*x^9 - 96*b₄^6*b₈*x^8 + 168*b₄^6*x^12 + 492*b₄^5*b₆^2*x^8 - 280*b₄^5*b₆*b₈*x^7 + 1704*b₄^5*b₆*x^11 - 116*b₄^5*b₈^2*x^6 - 784*b₄^5*b₈*x^10 + 888*b₄^5*x^14 + 1020*b₄^4*b₆^3*x^7 - 168*b₄^4*b₆^2*b₈*x^6 + 5895*b₄^4*b₆^2*x^10 - 300*b₄^4*b₆*b₈^2*x^5 - 1218*b₄^4*b₆*b₈*x^9 + 6138*b₄^4*b₆*x^13 - 40*b₄^4*b₈^3*x^4 - 767*b₄^4*b₈^2*x^8 - 4002*b₄^4*b₈*x^12 + 1101*b₄^4*x^16 + 1095*b₄^3*b₆^4*x^6 + 226*b₄^3*b₆^3*b₈*x^5 + 9762*b₄^3*b₆^3*x^9 - 241*b₄^3*b₆^2*b₈^2*x^4 + 2358*b₄^3*b₆^2*b₈*x^8 + 17127*b₄^3*b₆^2*x^12 - 72*b₄^3*b₆*b₈^3*x^3 - 444*b₄^3*b₆*b₈^2*x^7 - 6960*b₄^3*b₆*b₈*x^11 + 4164*b₄^3*b₆*x^15 - 4*b₄^3*b₈^4*x^2 - 4*b₄^3*b₈^3*x^6 - 3284*b₄^3*b₈^2*x^10 - 13196*b₄^3*b₈*x^14 - 408*b₄^3*x^18 + 642*b₄^2*b₆^5*x^5 + 346*b₄^2*b₆^4*b₈*x^4 + 8430*b₄^2*b₆^4*x^8 - 38*b₄^2*b₆^3*b₈^2*x^3 + 6172*b₄^2*b₆^3*b₈*x^7 + 23250*b₄^2*b₆^3*x^11 - 38*b₄^2*b₆^2*b₈^3*x^2 + 2232*b₄^2*b₆^2*b₈^2*x^6 + 4506*b₄^2*b₆^2*b₈*x^10 + 9876*b₄^2*b₆^2*x^14 - 4*b₄^2*b₆*b₈^4*x + 712*b₄^2*b₆*b₈^3*x^5 - 1272*b₄^2*b₆*b₈^2*x^9 - 28424*b₄^2*b₆*b₈*x^13 - 6852*b₄^2*b₆*x^17 + 102*b₄^2*b₈^4*x^4 + 120*b₄^2*b₈^3*x^8 - 9428*b₄^2*b₈^2*x^12 - 21272*b₄^2*b₈*x^16 - 1266*b₄^2*x^20 + 195*b₄*b₆^6*x^4 + 162*b₄*b₆^5*b₈*x^3 + 3654*b₄*b₆^5*x^7 + 29*b₄*b₆^4*b₈^2*x^2 + 4410*b₄*b₆^4*b₈*x^6 + 15021*b₄*b₆^4*x^10 - 4*b₄*b₆^3*b₈^3*x + 2728*b₄*b₆^3*b₈^2*x^5 + 12708*b₄*b₆^3*b₈*x^9 + 12216*b₄*b₆^3*x^13 - b₄*b₆^2*b₈^4 + 1112*b₄*b₆^2*b₈^3*x^4 + 6138*b₄*b₆^2*b₈^2*x^8 - 12312*b₄*b₆^2*b₈*x^12 - 9657*b₄*b₆^2*x^16 + 244*b₄*b₆*b₈^4*x^3 + 2224*b₄*b₆*b₈^3*x^7 - 8536*b₄*b₆*b₈^2*x^11 - 39600*b₄*b₆*b₈*x^15 - 8604*b₄*b₆*x^19 + 20*b₄*b₈^5*x^2 + 320*b₄*b₈^4*x^6 - 728*b₄*b₈^3*x^10 - 11840*b₄*b₈^2*x^14 - 14940*b₄*b₈*x^18 - 480*b₄*x^22 + 24*b₆^7*x^3 + 26*b₆^6*b₈*x^2 + 627*b₆^6*x^6 + 9*b₆^5*b₈^2*x + 1032*b₆^5*b₈*x^5 + 3663*b₆^5*x^9 + b₆^4*b₈^3 + 844*b₆^4*b₈^2*x^4 + 5265*b₆^4*b₈*x^8 + 5214*b₆^4*x^12 + 424*b₆^3*b₈^3*x^3 + 3928*b₆^3*b₈^2*x^7 + 2296*b₆^3*b₈*x^11 - 2616*b₆^3*x^15 + 123*b₆^2*b₈^4*x^2 + 1764*b₆^2*b₈^3*x^6 + 978*b₆^2*b₈^2*x^10 - 15420*b₆^2*b₈*x^14 - 7029*b₆^2*x^18 + 18*b₆*b₈^5*x + 402*b₆*b₈^4*x^5 + 820*b₆*b₈^3*x^9 - 8252*b₆*b₈^2*x^13 - 16326*b₆*b₈*x^17 - 2262*b₆*x^21 + b₈^6 + 34*b₈^5*x^4 + 171*b₈^4*x^8 - 980*b₈^3*x^12 - 4841*b₈^2*x^16 - 3598*b₈*x^20 - 3*x^24) * hR

set_option maxHeartbeats 4000000 in
theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y x4 y4 : K)
  (h : W.toAffine.Nonsingular x y) (h4 : W.toAffine.Nonsingular x4 y4),
  2 * y + W.a₁ * x + W.a₃ ≠ 0 →
  (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
    WeierstrassCurve.Affine.Point.some x4 y4 h4 →
  x4 * ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) *
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
        (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2) =
    x * ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) *
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
        (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2) -
    (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) *
      ((2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
        (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 -
        (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3) := by
  intro K _ _ W x y x4 y4 h h4 hD h4P
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hD' : y - W.toAffine.negY x y = (2 * y + W.a₁ * x + W.a₃) := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hyne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hD
    rw [← hD']
    exact sub_eq_zero.mpr hy
  have hL0 : W.toAffine.slope x x y y = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne, hD']
  obtain ⟨x2, y2, h2, hPP⟩ : ∃ (x2 y2 : K) (h2 : W.toAffine.Nonsingular x2 y2),
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x2 y2 h2 :=
    ⟨_, _, _, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne⟩
  have hx2e : x2 = W.toAffine.addX x x (W.toAffine.slope x x y y) ∧
      y2 = W.toAffine.addY x x y (W.toAffine.slope x x y y) := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne] at hPP
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hPP
    exact ⟨hPP.1.symm, hPP.2.symm⟩
  generalize hsg : W.toAffine.slope x x y y = s at hL0 hx2e
  have hs : s * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hL0]
    exact div_mul_cancel₀ _ hD
  have hx2 : x2 = s ^ 2 + W.a₁ * s - W.a₂ - 2 * x := by
    rw [hx2e.1]
    simp only [WeierstrassCurve.Affine.addX]
    ring
  have hb4W : W.b₄ = W.a₁ * W.a₃ + 2 * W.a₄ := by
    simp only [WeierstrassCurve.b₄]
    ring
  have hx2F := dbl_alg W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ W.b₂ W.b₄ W.b₆ W.b₈ x y s x2 rfl hb4W rfl rfl hE hs hx2
  have hE2 : y2 ^ 2 + W.a₁ * x2 * y2 + W.a₃ * y2 = x2 ^ 3 + W.a₂ * x2 ^ 2 + W.a₄ * x2 + W.a₆ := by
    have hx := h2.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have e4 : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x2 y2 h2 + WeierstrassCurve.Affine.Point.some x2 y2 h2 := by
    rw [← hPP]
    abel
  have hu2 : 2 * y2 + W.a₁ * x2 + W.a₃ ≠ 0 := by
    intro h0
    have hy2 : y2 = W.toAffine.negY x2 y2 := by
      rw [WeierstrassCurve.Affine.negY]
      linear_combination h0
    apply WeierstrassCurve.Affine.Point.some_ne_zero h4
    rw [← h4P, e4, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy2]
  have hy2ne : y2 ≠ W.toAffine.negY x2 y2 := by
    intro hy
    apply hu2
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  have hD2 : y2 - W.toAffine.negY x2 y2 = 2 * y2 + W.a₁ * x2 + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hL2 : W.toAffine.slope x2 x2 y2 y2 =
      (3 * x2 ^ 2 + 2 * W.a₂ * x2 + W.a₄ - W.a₁ * y2) / (2 * y2 + W.a₁ * x2 + W.a₃) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy2ne, hD2]
  have hX : (WeierstrassCurve.Affine.Point.some x4 y4 h4 : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x2 y2 h2 + WeierstrassCurve.Affine.Point.some x2 y2 h2 := by
    rw [← h4P]
    exact e4
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy2ne] at hX
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hX
  obtain ⟨hx4e, -⟩ := hX
  generalize hs2g : W.toAffine.slope x2 x2 y2 y2 = s2 at hL2 hx4e
  have hs2 : s2 * (2 * y2 + W.a₁ * x2 + W.a₃) = 3 * x2 ^ 2 + 2 * W.a₂ * x2 + W.a₄ - W.a₁ * y2 := by
    rw [hL2]
    exact div_mul_cancel₀ _ hu2
  have hx4 : x4 = s2 ^ 2 + W.a₁ * s2 - W.a₂ - 2 * x2 := by
    rw [hx4e]
    simp only [WeierstrassCurve.Affine.addX]
    ring
  have hx4F2 := dbl_alg W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ W.b₂ W.b₄ W.b₆ W.b₈ x2 y2 s2 x4 rfl hb4W rfl rfl hE2 hs2 hx4
  have hUF : (2 * y + W.a₁ * x + W.a₃) ^ 2 = (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination 4 * hE
  have hU2F : (2 * y2 + W.a₁ * x2 + W.a₃) ^ 2 = (4 * x2 ^ 3 + W.b₂ * x2 ^ 2 + 2 * W.b₄ * x2 + W.b₆) := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination 4 * hE2
  have hF0 : (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ≠ 0 := by
    rw [← hUF]
    exact pow_ne_zero 2 hD
  have hF2ne : (4 * x2 ^ 3 + W.b₂ * x2 ^ 2 + 2 * W.b₄ * x2 + W.b₆) ≠ 0 := by
    rw [← hU2F]
    exact pow_ne_zero 2 hu2
  have hFx2 : (4 * x2 ^ 3 + W.b₂ * x2 ^ 2 + 2 * W.b₄ * x2 + W.b₆) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3 = (4 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 + W.b₂ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) + 2 * W.b₄ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 + W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3) := by
    linear_combination (4 * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2 + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2) + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)) + 2 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2) * hx2F
  have hG0 : (4 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 + W.b₂ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) + 2 * W.b₄ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 + W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3) ≠ 0 := by
    rw [← hFx2]
    exact mul_ne_zero hF2ne (pow_ne_zero 3 hF0)
  have hx4G : x4 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * (4 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 + W.b₂ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) + 2 * W.b₄ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 + W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3) = ((x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 4 - W.b₄ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 - 2 * W.b₆ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3 - W.b₈ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4) := by
    linear_combination (-(x4 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))) * hFx2 + (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4 * hx4F2 + ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 3 + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 - W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)) - 2 * W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3) * hx2F
  have hR : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hid := ident_b W.b₂ W.b₄ W.b₆ W.b₈ x hR
  have hTG : (x4 * ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2) - x * ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2) + (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) * ((2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 - (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3)) * (4 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 + W.b₂ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) + 2 * W.b₄ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 + W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3) = 0 := by
    linear_combination (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2 * hx4G + hid
  have hT : (x4 * ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2) - x * ((4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2) + (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) * ((2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 - (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3)) = 0 := (mul_eq_zero.mp hTG).resolve_right hG0
  linear_combination hT

end MPP.Solutions.Bsd265
