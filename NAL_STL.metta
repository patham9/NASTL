;; UTILITIES ;;

(= (TupleConcat $Ev1 $Ev2) 
   (collapse (superpose ((superpose $Ev1)
                         (superpose $Ev2)))))

(= (any $Z)
   (not (== () $Z)))

(= (range $K $N)
   (If (< $K $N)
       (TupleConcat ($K) (range (+ $K 1) $N)) ()))

(= (firstTrue $ψ from $a to $b)
   (If (> $a $b)
       none
       (If ($ψ $a)
           $a
           (firstTrue $ψ from (+ 1 $a) to $b))))

;; PROPOSITIONAL LOGIC ;;

(= (∧ $P $Q)
   (and $P $Q))

(= (v $P $Q)
   (or $P $Q))

(= (¬ $P)
   (not $P))

(= (⟹ $P $Q)
   (v ((¬ $P) $Q)))

(= (⟺ $P $Q)
   (∧ ($P ⟹ $Q) ($Q ⟹ $P)))

;; QUANTIFIED PREDICATES OVER INTERVALS ;;

(= (∀x $ϕ from $a to $b)
   (If (> $a $b)
       True
       (and ($ϕ $a) (∀x $ϕ from (+ $a 1) to $b))))

(= (∃x $ϕ from $a to $b)
   (If (> $a $b)
       False
       (or ($ϕ $a) (∃x $ϕ from (+ 1 $a) to $b))))

;count true
(= (Tx $ϕ from $a to $b)
   (If (> $a $b)
       ()
       (let $rest (Tx $ϕ from (+ 1 $a) to $b)
            (If ($ϕ $a)
                (TupleConcat ($a) $rest)
                $rest))))

(= (Fx $ϕ from $a to $b)
   (If (> $a $b)
       ()
       (let $rest (Fx $ϕ from (+ 1 $a) to $b)
            (If (not ($ϕ $a))
                (TupleConcat ($a) $rest)
                $rest))))

;; SIGNAL TEMPORAL LOGIC ;;

;globally
(= (□ $ϕ from $a to $b at $t)
   (∀x $ϕ from (+ $t $a) to (+ $t $b)))

;finally
(= (◊ $ϕ from $a to $b at $t)
   (∃x $ϕ from (+ $t $a) to (+ $t $b)))

;until
(= (𝒰 $ϕ $ψ from $a to $b at $t)
   (any (collapse (let* (($I (range (+ $t $a) (+ $t $b)))
                         ($y (superpose $I)))
                        (If (and ($ψ $y) (∀x $ϕ from $t to $y)) thing)))))

;; SIGNAL TEMPORAL NAL

; Temporal ops with NAL truth value

(= (Truth_w2TV $wp $w)
   ((/ $wp $w)
    (/ $w (+ $w 1))))

;globally
(= (□TV $ϕ from $a to $b at $t)
   ((Tx $ϕ from (+ $t $a) to (+ $t $b))
    (range (+ $t $a) (+ 1 (+ $t $b)))))

;finally
(= (◊TV $ϕ from $a to $b at $t)
   (let $ival (range (+ $t $a) (+ (+ $t $b) 1))
        (If (◊ $ϕ from $a to $b at $t)
            ($ival ())
            (range (+ $t $a) (+ 1 (+ $t $b))))))

;until
(= (𝒰TV $ϕ $ψ from $a to $b at $t)
   (let $ts (firstTrue $ψ from (+ $t $a) to (+ $t $b))
        (If (== $ts none)
            (() (range $t (+ (+ $t $b) 1))) ;all false from t till t+b
            ((TupleConcat (range (+ 1 $ts) (+ (+ $t $b) 1)) ;true from ts+1 to t+b
                          (Tx $ϕ from $t to $ts)) ;points where ϕ holds within t and ts-1
             (range $t (+ 1 (+ $t $b))))))) ;points where ϕ does not hold within t and ts




;; EXAMPLE ;;

(= (x $t) $t)
(= (ϕ $t) (< (x $t) 10))
(= (ψ $t) (< (x $t) 20))

;!(□ ϕ from 1 to 10 at 0)
;!(let* (($I (range 1 6))
;        ($t (superpose $I)))
;       (□ ϕ from 1 to 5 at $t))
;!(□ ϕ from 1 to 10 at 0)
;!(𝒰 ϕ ψ from 0 to 13 at 5)
;!(□ ϕ from 1 to 10 at 0)

;!(□TV ϕ from 1 to 10 at 0)
;!(◊TV ϕ from 1 to 10 at 0)
;!(𝒰TV ϕ ψ from 1 to 10 at 0)

(= (∧TV ($pp1 $ptotal1) ($pp2 $ptotal2))
   ((collapse (intersection (superpose $pp1) (superpose $pp2)))
    (unique (union $ptotal1 $ptotal2))))

(= (TupleCount $tuple) (If (== $tuple ()) 0 (+ 1 (TupleCount (cdr-atom $tuple)))))

(= (Truth_fromSets ($P $T))
   (Truth_w2TV (TupleCount $P) (TupleCount $T)))

(= (𝒰TV_nested_helper ($ϕL $ϕ) $ψ from $a to $b at $t)
   (let $ts (firstTrue $ψ from (+ $t $a) to (+ $t $b)) ;last component ( $ψ )
        (If (not (== $ts none))
            (If (== $ϕL ())
                (TupleConcat (range (+ 1 $ts) (+ (+ $t $b) 1)) ;ts onwards plus
                             (Tx $ϕ from (+ $t $a) to (+ $t $ts)))    ;prior points where $ϕ holds
                (𝒰TV_nested_helper $ϕL $ϕ from $a to $ts at $t)))))

(= (𝒰TV_nested ($ϕL $ϕ) $ψ from $a to $b at $t)
   ((𝒰TV_nested_helper ($ϕL $ϕ) $ψ from $a to $b at $t)
    (range $t (+ $t (+ 1 $b)))))

;!(Truth_fromSets (□TV safe from 0 to 179 at 0))
;!(Truth_fromSets (𝒰TV_nested ((() A) B) C from 0 to 179 at 0))
;!(Truth_fromSets (∧TV (□TV safe from 0 to 179 at 0) (𝒰TV_nested ((() A) B) C from 0 to 179 at 0)))

!(□TV safe from 0 to 179 at 0)
!(𝒰TV_nested ((() A) B) C from 0 to 179 at 0)

!(Truth_fromSets (∧TV (□TV safe from 0 to 179 at 0)
                      (𝒰TV_nested ((() A) B) C from 0 to 179 at 0)))

;!(Truth_fromSets (∧TV (𝒰TV A B from 0 to 179 at 0) (𝒰TV B C from 0 to 179 at 0)))
;!(𝒰TV B C from 0 to 179 at 0)
;!(Truth_fromSets (∧TV (□TV safe from 0 to 179 at 0)
;                      (∧TV (𝒰TV A B from 0 to 179 at 0) (𝒰TV B C from 0 to 179 at 0))))

;!(𝒰TV safeA safeB from 0 to 9 at 0)
;!(□TV safeA from 0 to 9 at 0)
;!(□TV safeB from 0 to 9 at 0)

;!(∧TV (□TV A from 0 to 179 at 0) (□TV B from 0 to 179 at 0))
;!(∧TV (𝒰TV A B from 0 to 179 at 0) (□TV safe from 0 to 9 at 0))

;todo in mettamorph
;(= (intersection $a $a) $a)

;!(𝒰TV safeA safeB from 0 to 9 at 0)
;;safeB is fulfilled in t=6 for first time, however A does not hold so safeA does not
;;meaning 0, 2, 4 is positive evidence (safe and A), and 7, 8, 9 despite 7 and 9 not being safe
;!(∧TV (𝒰TV A B from 0 to 9 at 0) (□TV safe from 0 to 9 at 0))
;;here 0, 2, 4 is positive evidence, and 8.
;;Additionally 6 is positive evidence, as 6 is safe, and B is fulfilled at 5 already

;(= (BC) (𝒰 B C from 0 to 179 at 0))
;(= (nestedABC) (𝒰 A nestedBC from 0 to 179 at 0))

;!(Truth_fromSets (𝒰TV safeA safeB from 0 to 9 at 0))
;!(∧TV (□TV safe from 0 to 179 at 0) (∧TV (𝒰TV A B from 0 to 179 at 0) (𝒰TV B C from 0 to 179 at 0)))
;!(Truth_fromSets (∧TV (□TV safe from 0 to 179 at 0) (∧TV (𝒰TV A B from 0 to 179 at 0) (𝒰TV B C from 0 to 179 at 0))))

;!(Truth_fromSets (∧TV (□TV safe from 0 to 179 at 0) (∧TV (𝒰TV A B from 0 to 179 at 0) (𝒰TV B C from 0 to 179 at 0))))

