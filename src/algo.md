seek current stack drag:
    node = nodes[current] or empty
    let epsilon = node.epsilon
    let rest = node \ epsilon
    if epsilon:
        drag += rest
        (current, current.parent) = (current.parent, current.parent.parent)
    else:
        if stack empty:
            current
        else s <- pop stack:
            seek s
            current = rest[s]; insert if empty

find id:
    seek root[id] stack[id] empty

union a b:
    a' <- find a
    b' <- find b
    if a /= b:
        let (larger, smaller) = (a, b) by rank
        smaller.epsilon = larger
        if ranks are equal:
            larger.rank += 1

insert f:
    seek root[f] stack[f] empty

extract:
    loop over only saturated nodes
    compute fixpoint...