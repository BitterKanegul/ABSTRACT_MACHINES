#lang racket
(require racket/cmdline)
(require json)



;; Abstract store and instrumentation updates
; For k-cfa, we want to store the last k call sites as our instrumentation and use it with the allocator
; I tack the instrumentation on with the state so that the new state consists of (E/A expr env k-ptr inst)
;
;
; What is a CALL SITE:
;  Im taking the definition from https://thomas.gilray.org/pdf/allocation-polyvariance.pdf
;   (ef ,e-args ...) is a call-site for ef at point expr
;   Upon finishing execution, pop the call-site? i think the stack of execution kinda handles it
;
;

;the k in k-cfa
(define k 1)
(define (update-callsites queue site)
  (define queue+ (append queue `(,site)))
  (if (> (length queue+) k)
      (rest queue+)
      queue+
      )
  )
(define (get x env store)
  (hash-ref store (hash-ref env x)))

(define (kalloc kont instrumentation)
  `(kalloc ,kont ,instrumentation))

(define (xalloc var instrumentation)
  `(xalloc ,var))


;join on a store
(define (store-update store kaddr kont)
  (hash-set store kaddr (set-add (hash-ref store kaddr (set)) kont)))
(define (store-bind store xaddrs vs)
  (foldl
   (λ (k v acc) (store-update acc k v))
   store
   xaddrs
   vs
   ))
(define (store-merge store store_delta)
  (define all-addrs
    (set-union
     (list->set (hash-keys store))
     (list->set (hash-keys store_delta))))
  (foldl
   (λ (addr acc)
     (hash-set
      acc
      addr
      (set-union
       (hash-ref store addr (set))
       (hash-ref store_delta addr (set))
       )))
   (hash)
   (set->list all-addrs)
   )
  )
(define (add-kont kont inst stores)
  (define kaddr (kalloc kont inst))
  `(,kaddr ,(store-update stores kaddr kont))
  )


(define (step-eval state stores)
  (match-define `(,tag ,expr ,env ,k-ptr ,inst) state)
  (match expr
    [(? symbol? x)
     `(
       ,(list->set (set-map (get x env stores)
                            (λ (v)
                              `(A ,v ,k-ptr ,inst))))
       ,stores
       )
     ]
    [`(λ (,xs ...) ,e)
     `(
       ,(set `(A (Clo (λ (,@xs) ,e) ,env) ,k-ptr ,inst))
       ,stores
       )]
    [(? boolean? b)
     `(
       ,(set `(A ,b ,k-ptr ,inst))
       ,stores
       )
     ]
    [(? integer? i)
     `(
       ,(set `(A ,i ,k-ptr ,inst))
       ,stores
       )]
    [`(if ,g ,t ,f)
     (match-define `(,k-ptr+ ,store+) (add-kont `(IF ,t ,f ,env ,k-ptr) inst stores))
     `(
       ,(set `(E ,g ,env ,k-ptr+ ,inst))
       ,store+
       )]
    [`(prim ,op ,es ...)
     (match-define `(,k-ptr+ ,store+) (add-kont `(ARG-PRIM ,op ,(rest es) () ,env ,k-ptr) inst stores))
     `(
       ,(set `(E ,(first es) ,env ,k-ptr+ ,inst))
       ,store+
       )
     ]
    [`(,f ,args ...)                               ; Update the instrumentation here
     (match-define `(,k-ptr+ ,store+) (add-kont `(ARG ,args () ,env ,k-ptr) inst stores))
     ;For Pushdown precision, we use the new environment and the new environment as our instrumentation
     `(
       ,(set `(E ,f ,env ,k-ptr+ ,(update-callsites inst `(,f ,env))))
       ,store+
       )
     ]
    [`(let ([,x ,e]) ,e-b)
     (match-define `(,k-ptr+ ,store+) (add-kont `(ARG () (Clo (λ (,x) ,e-b) ,env) ,k-ptr) inst stores))

     `(
       ,(set `(E ,e ,env ,k-ptr+ ,inst))
       ,store+
       )]
    ))


(define (step-apply expr k stores inst)
  (match k
    [`(ARG-PRIM ,op () ,vs ,env+ ,k-ptr)
     (define vs+ (append vs (list expr)))
     (define v-r (apply (eval op (make-base-namespace)) vs+))
     `( (A ,v-r ,k-ptr ,inst)
        ,stores)
     ]
    [`(ARG-PRIM ,op ,es ,vs ,env+ ,k-ptr)
     (match-define `(,k-ptr+ ,store+)
       (add-kont
        `(ARG-PRIM ,op ,(rest es) ,(append vs (list expr)) ,env+ ,k-ptr) inst stores))
     `(
       (E ,(first es) ,env+ ,k-ptr+ ,inst)
       ,store+)
     ]

    [`(ARG () ,vs ,env ,k-ptr)
     (define f (first vs))
     (define vs+ (append (rest vs) (list expr)))
     (match f
       [`(Clo (λ (,xs ...) ,e) ,env+)
        ;;Bind ,xs to new environment and add to store
        (define addrs (map (λ (x) (xalloc x inst)) xs))
        (define env++
          (foldl
           (λ (x addr acc) (hash-set acc x addr))
           env+
           xs
           addrs
           ))
        `( (E ,e ,env++ ,k-ptr ,inst)
           ,(store-bind stores addrs vs+)
           )])
     ]

    [`(ARG ,es ,vs ,env+ ,k-ptr)
     (match-define `(,k-ptr+ ,store+)
       (add-kont
        `(ARG ,(rest es) ,(append vs (list expr)) ,env+ ,k-ptr) inst stores))
     `(
       (E ,(first es) ,env+  ,k-ptr+ ,inst)
       ,store+)
     ]
    [`(IF ,t ,f ,env+ ,k-ptr)
     (if expr
         `(
           (E ,t ,env+ ,k-ptr ,inst)
           ,stores )
         `(
           (E ,f ,env+ ,k-ptr ,inst)
           ,stores ))]
    ))

;Performs apply on each kont found at k-ptr
(define (step-apply* state stores)
  (match-define `(,tag ,expr ,k-ptr ,inst) state)
  (define ks (set->list (hash-ref stores k-ptr)))
  ;;(set-of-states x store-updates)
  (define results (map (λ (k) (step-apply expr k stores inst)) ks))
  (define states+ (list->set (map first results)))
  (define stores+ (foldl (λ (s acc) (store-merge acc s)) stores (map second results)))

  `(,states+ ,stores+)
  )

;; The Abstract Apply-Eval Machine
(define (step-machine state stores)
  (match (first state)
    ['E (step-eval state stores)]
    ['A (step-apply* state stores)])
  )

; State x Store x Instrumentation -> Set<State> x Store x Set<Instrumentation>



;;adds edges from graph-delta to graph
; adds new nodes from graph-delta to graph
(define (graph-merge graph graph-delta)
  ;add all edges from delta
  (define graph+ (hash-map/copy
                  graph
                  (λ (k v)
                    (values k (set-union v (hash-ref graph-delta k (set)))))))
  ; Make a set of all the nodes on rhs
  (define reached-nodes
    (foldl
     (λ (v acc) (set-union acc v))
     (set)
     (hash-values graph-delta)))
  ;add new nodes to graph+
  (foldl
   (λ (n acc) (hash-set acc n (set)))
   graph+
   (set->list (set-subtract reached-nodes (list->set (hash-keys graph))))
   )
  )





;; Graph x Stores Fixpoint iteration
(define (graph-step graph stores)
  ; map-graph applies a function with same extra args to each node
  (define step_graph (hash-map/copy graph (λ (k _) (values k (step-machine k stores)))))
  ;((node -> (result x store))
  (define graph_update (hash-map/copy step_graph (λ (k v) (values k (first v)))))
  (define store_updates (hash-map step_graph (λ (_ v) (second v))))
  (define graph+ (graph-merge graph graph_update))
  (define stores+
    (foldl
     (λ (s acc)
       (store-merge acc s))
     stores
     store_updates))
  `(,graph+ ,stores+)
  )

(define (fixpoint graph-stores)
  (define (h g s)
    (match-define `(,g+ ,s+) (graph-step g s))
    (if (and (equal? g g+) (equal? s s+))
        `(,g ,s)
        (h g+ s+)
        ))
  (match-define `(,graph ,stores) graph-stores)
  (h graph stores))

(define (inj-graph-store program)
  `(,(hash `(E ,program ,(hash) Done ()) (set)) ,(hash 'Done (set))))

;; Graphviz DOT file generation for k-CFA analysis results

;; Helper: escape strings for DOT format
(define (escape-dot-string s)
  (string-replace
   (string-replace
    (string-replace (~a s) "\"" "\\\"")
    "\n" "\\n")
   "{" "\\{"))
;; '-' messes up graphviz
(define (number->dot-string n)
  (if (negative? n)
      (format "n~a" (abs n))
      (~a n)))
;; Helper: create a unique node ID
(define (state->node-id state)
  ;(define str (~a state))
  (define hash-val (equal-hash-code state))
  (format "node_~a" (number->dot-string hash-val)))

;; Helper: format state for label
(define (state->label state)
  (match state
    [`(E ,expr ,env ,k-ptr ,inst)
     (format "E\\n~a\\nκ: ~a\\ninst: ~a"
             (escape-dot-string expr)
             (escape-dot-string k-ptr)
             (escape-dot-string inst))]
    [`(A ,val ,k-ptr ,inst)
     (format "A\\n~a\\nκ: ~a\\ninst: ~a"
             (escape-dot-string val)
             (escape-dot-string k-ptr)
             (escape-dot-string inst))]
    [else (escape-dot-string state)]))

;; Helper: get color based on state type
(define (state->color state)
  (match state
    [`(E ,_ ,_ ,_ ,_) "lightblue"]
    [`(A ,_ ,_ ,_) "lightgreen"]
    [else "white"]))

;; Helper: format store entry for display
(define (format-store-entry addr values)
  (format "~a →\\n  ~a"
          (escape-dot-string addr)
          (escape-dot-string
           (string-join
            (map ~a (set->list values))
            "\\n  "))))

;; Main function: write graph and stores to DOT file
(define (write-graphviz-file graph stores filename)
  (with-output-to-file filename
    #:exists 'replace
    (λ()
      (displayln "digraph KCFA {")
      (displayln "  rankdir=LR;")
      (displayln "  node [shape=box, style=filled];")
      (newline)

      ;; Write all nodes with labels
      (displayln "  // Nodes")
      (for ([state (hash-keys graph)])
        (define node-id (state->node-id state))
        (define label (state->label state))
        (define color (state->color state))
        (printf "  ~a [label=\"~a\", fillcolor=~a];~n"
                node-id label color))
      (newline)

      ;; Write all edges
      (displayln "  // Edges")
      (for ([(source targets) (in-hash graph)])
        (define source-id (state->node-id source))
        (for ([target (in-set targets)])
          (define target-id (state->node-id target))
          (printf "  ~a -> ~a;~n" source-id target-id)
          ; ;TEST
          ; (printf "  ~a -> ~a;~n" source target)
          ))
      (newline)

      ;; Write store as a separate subgraph
      (displayln "  // Store")
      (displayln "  subgraph cluster_store {")
      (displayln "    label=\"Abstract Store\";")
      (displayln "    style=filled;")
      (displayln "    fillcolor=lightyellow;")
      (displayln "    node [shape=note, fillcolor=white];")
      (newline)
      (for ([(addr values) (in-hash stores)])
        (when (not (set-empty? values))
          (define store-id (format "store_~a" (equal-hash-code (~a addr))))
          (define label (format-store-entry addr values))
          (printf "    ~a [label=\"~a\"];~n" store-id label)))
      (displayln "  }")

      (displayln "}"))))

;; Convenience function: analyze and visualize
(define (analyze-and-visualize program output-file)
  (match-define `(,graph ,stores) (fixpoint (inj-graph-store program)))
  (write-graphviz-file graph stores output-file)
  (printf "Graphviz DOT file written to: ~a~n" output-file)
  (printf "Render with: dot -Tpng ~a -o output.png~n" output-file)
  `(,graph ,stores))

;; Example usage (add to end of your file):
;; (define result (fixpoint (inj-graph-store program)))
;; (write-graphviz-file (first result) (second result) "output.dot")

;; Result debugging and visualization
(define cfa-file
  (command-line
   #:program "CFA-analyser"
   #:args (filename)
   filename
   ))
(define (run-program filename)
  (match-define `(,graph ,stores)  (fixpoint (inj-graph-store (with-input-from-file filename read))))
  (write-graphviz-file graph stores "output2.dot")
  )
(if (file-exists? cfa-file)
    (run-program cfa-file)
    (error "File not found")
    )






;; Datastructures that we need
; Set
;   (set-equal?)
;   (set)
;   (set v)
;   (set-member?)
;   (set-add)
;   (set-union)
;   (set->list)
;   (list->set)
;   (set-count)
;   (set-first)
;   (set-rest)
;   (set-union)
;   (set-intersect)
;   (set-subtract)
;   (set-map)
;   (subset?)
;
; Hashmap
;   (hash)
;   (hash-set)
;   (hash-ref)
;   (hash-update)
;   (hash-remove)
;   (hash-keys)
;   (hash-values)
; Treelist
;   RRB trees used to allow log N insertions, access by index, replacing element, dropping from start or end
; Graph
;   I implement it as an adjacency list
;   Graph : Hashmap<Node, Set<Node>>
;      (graph-keys)
;      (graph-values)
;      (graph-merge)
;      (graph-map)
;      (graph-pretty-print)
;      (graph)
;
; Circular queue
;       (kqueue k)
;       (kqueue->list)
;       (kqueue-insert)
;       (kqueue-pop)
;       (kqueue-capacity)
;
; Union Find
;
