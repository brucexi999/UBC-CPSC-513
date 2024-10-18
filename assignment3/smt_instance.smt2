(set-logic ALL)
(set-option :produce-models true)
(set-option :incremental true)
(set-option :produce-unsat-cores true)
(set-option :print-cores-full true)

; Declare array elements as symbolic variables
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)

; Sorting logic
(declare-const arr0_0 Int)
(declare-const arr0_1 Int)
(declare-const arr0_2 Int)
(declare-const arr0_3 Int)
(declare-const arr0_4 Int)
(declare-const arr0_5 Int)

(assert (or 
 (and (= arr0_0 x0) (<= x0 x1) (<= x0 x2) (<= x0 x3) (<= x0 x4) (<= x0 x5)) ; if x0 is min
 (and (= arr0_0 x1) (<= x1 x0) (<= x1 x2) (<= x1 x3) (<= x1 x4) (<= x1 x5)) ; if x1 is min
 (and (= arr0_0 x2) (<= x2 x0) (<= x2 x1) (<= x2 x3) (<= x2 x4) (<= x2 x5)) ; if x2 is min
 (and (= arr0_0 x3) (<= x3 x0) (<= x3 x1) (<= x3 x2) (<= x3 x4) (<= x3 x5)) ; if x3 is min
 (and (= arr0_0 x4) (<= x4 x0) (<= x4 x1) (<= x4 x2) (<= x4 x3) (<= x4 x5)) ; if x4 is min
 (and (= arr0_0 x5) (<= x5 x0) (<= x5 x1) (<= x5 x2) (<= x5 x3) (<= x5 x4)) ; if x5 is min
))

(declare-const arr1_0 Int)
(declare-const arr1_1 Int)
(declare-const arr1_2 Int)
(declare-const arr1_3 Int)
(declare-const arr1_4 Int)
(declare-const arr1_5 Int)

(assert (= arr1_0 arr0_0))

(assert (or 
 (and (= arr1_1 arr0_1) (<= arr0_1 arr0_2) (<= arr0_1 arr0_3) (<= arr0_1 arr0_4) (<= arr0_1 arr0_5))
 (and (= arr1_1 arr0_2) (<= arr0_2 arr0_1) (<= arr0_2 arr0_3) (<= arr0_2 arr0_4) (<= arr0_2 arr0_5))
 (and (= arr1_1 arr0_3) (<= arr0_3 arr0_1) (<= arr0_3 arr0_2) (<= arr0_3 arr0_4) (<= arr0_3 arr0_5))
 (and (= arr1_1 arr0_4) (<= arr0_4 arr0_1) (<= arr0_4 arr0_2) (<= arr0_4 arr0_3) (<= arr0_4 arr0_5))
 (and (= arr1_1 arr0_5) (<= arr0_5 arr0_1) (<= arr0_5 arr0_2) (<= arr0_5 arr0_3) (<= arr0_5 arr0_4))
))

(declare-const arr2_0 Int)
(declare-const arr2_1 Int)
(declare-const arr2_2 Int)
(declare-const arr2_3 Int)
(declare-const arr2_4 Int)
(declare-const arr2_5 Int)

(assert (= arr2_0 arr0_0))
(assert (= arr2_1 arr1_1))

(assert (or 
 (and (= arr2_2 arr1_2) (<= arr1_2 arr1_3) (<= arr1_2 arr1_4) (<= arr1_2 arr1_5))
 (and (= arr2_2 arr1_3) (<= arr1_3 arr1_2) (<= arr1_3 arr1_4) (<= arr1_3 arr1_5))
 (and (= arr2_2 arr1_4) (<= arr1_4 arr1_2) (<= arr1_4 arr1_3) (<= arr1_4 arr1_5))
 (and (= arr2_2 arr1_5) (<= arr1_5 arr1_2) (<= arr1_5 arr1_3) (<= arr1_5 arr1_4))
))

(declare-const arr3_0 Int)
(declare-const arr3_1 Int)
(declare-const arr3_2 Int)
(declare-const arr3_3 Int)
(declare-const arr3_4 Int)
(declare-const arr3_5 Int)

(assert (= arr3_0 arr0_0))
(assert (= arr3_1 arr1_1))
(assert (= arr3_2 arr2_2))

(assert (or 
 (and (= arr3_3 arr2_3) (<= arr2_3 arr2_4) (<= arr2_3 arr2_5))
 (and (= arr3_3 arr2_4) (<= arr2_4 arr2_3) (<= arr2_4 arr2_5))
 (and (= arr3_3 arr2_5) (<= arr2_5 arr2_3) (<= arr2_5 arr2_4))
))

(declare-const arr4_0 Int)
(declare-const arr4_1 Int)
(declare-const arr4_2 Int)
(declare-const arr4_3 Int)
(declare-const arr4_4 Int)
(declare-const arr4_5 Int)

(assert (= arr4_0 arr0_0))
(assert (= arr4_1 arr1_1))
(assert (= arr4_2 arr2_2))
(assert (= arr4_3 arr3_3))

(assert (or 
 (and (= arr4_4 arr3_4) (<= arr3_4 arr3_5))
 (and (= arr4_4 arr3_5) (<= arr3_5 arr3_4))
))


; Check if the array is sorted
(assert (and (<= arr4_0 arr4_1) (<= arr4_1 arr4_2) (<= arr4_2 arr4_3) (<= arr4_3 arr4_4) (<= arr4_4 arr4_5)))

(assert (not (and (<= arr4_0 arr4_1) (<= arr4_1 arr4_2) (<= arr4_2 arr4_3) (<= arr4_3 arr4_4) (<= arr4_4 arr4_5))))
(check-sat)
(get-model)	; See the counter-example