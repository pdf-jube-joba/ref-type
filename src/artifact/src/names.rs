//! Synthetic frontend names carry identities even where a consumer stores only spelling.
pub(crate) fn relocate(value: &mut String, r: &mut crate::Relocation) -> crate::Result<()> {
    if !value.contains('<') {
        return Ok(());
    }
    let prefixes = [
        ("<macro:", "resolve.hygiene"),
        ("<macro-use:", "resolve.binding"),
        ("<temporary:", "resolve.expression"),
    ];
    let mut cursor = 0;
    while let Some((start, prefix, space)) = prefixes
        .iter()
        .filter_map(|(prefix, space)| {
            value[cursor..]
                .find(prefix)
                .map(|offset| (cursor + offset, *prefix, *space))
        })
        .min_by_key(|(offset, _, _)| *offset)
    {
        let first = start + prefix.len();
        let end = first
            + value[first..]
                .find([':', '>'])
                .unwrap_or(value.len() - first);
        let Ok(old) = value[first..end].parse::<u64>() else {
            cursor = first;
            continue;
        };
        // The fixed macro validation probe never enters the session allocator.
        if space == "resolve.hygiene" && old == u64::MAX {
            cursor = end;
            continue;
        }
        let new = r.id(space, old)?.to_string();
        value.replace_range(first..end, &new);
        cursor = first + new.len();
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nested_synthetic_names_keep_the_same_identity_mapping() {
        let mut r = crate::Relocation::default();
        r.insert("resolve.hygiene", 1, 12).unwrap();
        r.insert("resolve.binding", 7, 19).unwrap();
        let mut name = "<structure:<macro:1:Thing>:<macro-use:7>>".to_string();
        relocate(&mut name, &mut r).unwrap();
        assert_eq!(name, "<structure:<macro:12:Thing>:<macro-use:19>>");
    }
}
