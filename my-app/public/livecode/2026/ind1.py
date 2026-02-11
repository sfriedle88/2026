
# (Example borrowed from Aaron Bradley -- re: a 15yr old algorithm)
# Is the property "y >= 1" always true in the loop? I.e., is "y >= 1" an invariant? 
#    Yes. It's a trivial example.
# Real systems are more complex, and the idea goes way beyond Forge (though we could use
# Forge for this up to limits on integer size). 
# Let's use this as practice with using the inductive method.

def f1():
    x = 1          # Initial State (part 1)
    y = 1          # Initial State (part 2)
    while True:
        assert(y >= 1) # the invariant
        print(f'x: {x}, y: {y}') # uncomment if you aren't sure how the below works
        # Transition (one line so both run based on last loop's values)
        x, y = x + 1, y + x  
f1()

# Base case (called "initiation" in some textbooks)
#   FILL: (initial state condition) implies (property goal)
pred initiation {
    (x = 1 and y = 1) implies (y >= 1)
}
#   FILL: (Does this implication hold? If not, why not?)

# Inductive case (called "consecution" in some textbooks)
# Suggestion: 2 states involved, so use x_pre, x_post, y_pre, y_post.
#   FILL: (P holds of pre-state) and (transition taken) implies (P holds of post-state)
... (y_pre >= 1 and x_pre >= 0) and (
    x_post = x_pre + 1 and 
    y_post = y_pre + x_pre
    implies (y_post >= 1)
#   FILL: (Does this implication hold? If not, why not?)


