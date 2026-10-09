-- Layout-only transformations. Mathematical source is passed through intact.
local function latex_escape(s)
  local map = {['\\']='\\textbackslash{}', ['{']='\\{', ['}']='\\}', ['#']='\\#',
    ['$']='\\$', ['%']='\\%', ['&']='\\&', ['_']='\\_', ['~']='\\textasciitilde{}', ['^']='\\textasciicircum{}'}
  return (s:gsub('[\\{}#$%%&_~^]', map))
end

function Code(el)
  if FORMAT:match('latex') then
    -- \seqsplit drops spaces and may break anywhere, so keep ordinary words
    -- whole and let only long tokens (hashes, paths) break between characters;
    -- words are rejoined with breakable interword spaces.
    local words = {}
    for word in el.text:gmatch('%S+') do
      if #word > 18 then
        table.insert(words, '\\seqsplit{' .. latex_escape(word) .. '}')
      else
        table.insert(words, latex_escape(word))
      end
    end
    return pandoc.RawInline('latex', '\\paperinlinecode{' .. table.concat(words, '\\ ') .. '}')
  end
end

function CodeBlock(el)
  if el.classes:includes('mermaid') then
    return {} -- Original design syntax is not printable art.
  end
end

function Image(el)
  if FORMAT:match('latex') then
    if el.src:match('%.png$') then
      local p = el.src:gsub('%.png$', '-r10.pdf')
      local f = io.open(p, 'rb')
      if not f then
        p = el.src:gsub('%.png$', '.pdf')
        f = io.open(p, 'rb')
      end
      if f then f:close(); el.src = p end
    elseif el.src:match('%.svg$') then
      local p = el.src:gsub('%.svg$', '.pdf')
      local f = io.open(p, 'rb')
      if f then f:close(); el.src = p end
    end
    el.attributes.width = nil
    el.attributes.height = nil
  end
  return el
end

-- Links into the local writing workspace (claims tables, audits, sibling drafts)
-- do not exist for a preprint reader; print their text only. Web, mail and
-- in-document anchors stay live.
function Link(el)
  local t = el.target
  if t:match('^https?://') or t:match('^mailto:') or t:match('^#') then return nil end
  return el.content
end

function Figure(el)
  if not FORMAT:match('latex') then return nil end
  local content = pandoc.Pandoc(el.content):walk({Image = function(img)
    return pandoc.RawInline('latex', '\\includegraphics[width=\\linewidth,height=0.62\\textheight,keepaspectratio]{'
       .. img.src .. '}')
  end})
  local body = pandoc.write(content, 'latex')
  local cap = ''
  if el.caption and el.caption.long and #el.caption.long > 0 then
    cap = pandoc.write(pandoc.Pandoc(el.caption.long), 'latex')
  end
  -- Keep a plate and its caption beside the discussion that introduces it;
  -- pending figures must not be flushed onto a sparse appendix float page.
  return pandoc.RawBlock('latex', '\\begin{figure}[H]\n\\centering\n' .. body .. '\n'
    .. (#cap > 0 and ('\\caption*{' .. cap .. '}\n') or '') .. '\\end{figure}')
end

local function merge_figure_caption(blocks)
  local result = pandoc.List()
  local i = 1
  while i <= #blocks do
    local block = blocks[i]
    local following = blocks[i + 1]
    if block.t == 'Figure' and following and following.t == 'Para' then
      local caption_text = pandoc.utils.stringify(following)
      -- Lua quantifiers operate on bytes: '附?' does not make a whole UTF-8
      -- character optional. Match ordinary and appendix captions separately.
      if caption_text:match('^图%s*%u?%d') or caption_text:match('^附图%s*%u?%d')
        or caption_text:match('^Figure%s*%u?%d') then
        -- The explanatory caption already carries the figure number and title.
        -- Preserve the image's alt text in Markdown, but do not print it twice.
        block.caption.long = pandoc.Blocks{following}
        result:insert(block)
        i = i + 2
      else
        result:insert(block)
        i = i + 1
      end
    else
      result:insert(block)
      i = i + 1
    end
  end
  return result
end

local function keep_table_intro(blocks)
  local result = pandoc.List()
  for i, block in ipairs(blocks) do
    local next_block = blocks[i+1]
    if block.t == 'Para' and next_block then
      if next_block.t == 'Table' then
        result:insert(pandoc.RawBlock('latex', '\\Needspace{7\\baselineskip}'))
      elseif next_block.t == 'OrderedList' or next_block.t == 'BulletList' then
        local text = pandoc.utils.stringify(block)
        if text:match('^定理') or text:match('^定义') or text:match('^命题')
          or text:match('^Theorem') or text:match('^Definition') or text:match('^Proposition') then
          result:insert(pandoc.RawBlock('latex', '\\Needspace{8\\baselineskip}'))
        end
      end
    end
    result:insert(block)
  end
  return result
end

return {
  {Code=Code, CodeBlock=CodeBlock, Image=Image, Link=Link},
  {Blocks=merge_figure_caption},
  {Blocks=keep_table_intro},
  {Figure=Figure}
}
